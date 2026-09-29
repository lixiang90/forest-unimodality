import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell151.Parameters
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q47737_90312.Batch000_049
import ForestUnimodality.BinomialMassData.Q47737_90312.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree000.table
  base := (194437510850024900205212933/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1194286214250627337074561800000000000000)
      linear := (-69207914301644040191985319000000000000)
      constant := (388875021700049800410425866000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree000.table
  base := (194437510850024900205212933/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1194286214250627337074561800000000000000)
      linear := (-69207914301644040191985319000000000000)
      constant := (388875021700049800410425866000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree001.table
  base := (26796851306518535565551711382685721430927/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-2389844134155811829428187494132344000000000000)
      constant := (385456548065545923612878677578467429226560796616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree001.table
  base := (6697789919554698558297488876386046770833/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-2390437545118517609886296417026719000000000000)
      constant := (385375149331452571588499027407225372195310853856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24959129473215556711/50000000000000000000)
  directionHi := (49918258946431113423/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree002.table
  base := (4986398152965558277252348484835726449531/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-4655463453327973387269730747940319000000000000)
      constant := (226284288659232647275704037172533763657802949525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree002.table
  base := (24922658100991320017843888579229533852857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-4656650275253384948185948593729069000000000000)
      constant := (226201819168811098089188104560428386843597625035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24959129473215556711/50000000000000000000)
  centralHi := (49918258946431113423/100000000000000000000)
  directionLo := (35297539406047483679/50000000000000000000)
  directionHi := (70595078812094967359/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree003.table
  base := (77050911240052482789153353888895342257443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-769009196944459438345697111305366000000000000)
      constant := (15987460757801058526784867295734725070732174477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree003.table
  base := (77013975702478484759654854423212468212659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-769207000598694698498400085603491000000000000)
      constant := (15980413725734671733718437679436475697864498301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35297539406047483679/50000000000000000000)
  centralHi := (70595078812094967359/100000000000000000000)
  directionLo := (4323048036029917191/5000000000000000000)
  directionHi := (86460960720598343821/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree004.table
  base := (12648264113734637658717719765535289687211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-9186702091672296502952817255556269000000000000)
      constant := (100652595215476755497996930346316254787396286644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree004.table
  base := (25282965908323713227742721189064915317093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-9189075735523119624785252947133769000000000000)
      constant := (100608994567519192240516093687985756126662794886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4323048036029917191/5000000000000000000)
  centralHi := (86460960720598343821/100000000000000000000)
  directionLo := (19967303578572445369/20000000000000000000)
  directionHi := (49918258946431113423/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree005.table
  base := (174787824139960865336415414579525880977/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-11452321410844458060794360509364244000000000000)
      constant := (78040899727196780605771191477794307698359425400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree005.table
  base := (8734446462713739696470258053657959545103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-11455288465657986963084905123836119000000000000)
      constant := (78013323984897174643651555647602665073768699812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19967303578572445369/20000000000000000000)
  centralHi := (49918258946431113423/50000000000000000000)
  directionLo := (22324124064531400529/20000000000000000000)
  directionHi := (55810310161328501323/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree006.table
  base := (3127589078771291159071969672593649676647/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-1524215636668513290959544862574691000000000000)
      constant := (7428358591577789201289995829733391432886408264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree006.table
  base := (12502939606591872668446183304434652113307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-1524611243976983811264950811170941000000000000)
      constant := (7426666185613930877701965734564287415651669546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22324124064531400529/20000000000000000000)
  centralHi := (55810310161328501323/50000000000000000000)
  directionLo := (24454852653375525389/20000000000000000000)
  directionHi := (61137131633438813473/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree007.table
  base := (1138419517334073396785425286533683880777/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-15983560049188781176477447016980194000000000000)
      constant := (62486525114568862780496584558049601804002910832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree007.table
  base := (9101542436069917725368412029850742582123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-15987713925927721639684209477240819000000000000)
      constant := (62481142392096703780376927332319442247048521946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24454852653375525389/20000000000000000000)
  centralHi := (61137131633438813473/50000000000000000000)
  directionLo := (132071299053581846931/100000000000000000000)
  directionHi := (33017824763395461733/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree008.table
  base := (1653920626218169642440655672580505856533/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-18249179368360942734318990270788169000000000000)
      constant := (62586640426252713984100580998918227041518119064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree008.table
  base := (330545645730364412711766196577648101757/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-18253926656062588977983861653943169000000000000)
      constant := (62589727508561047759803547771683418515873156280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132071299053581846931/100000000000000000000)
  centralHi := (33017824763395461733/25000000000000000000)
  directionLo := (141190157624189934717/100000000000000000000)
  directionHi := (70595078812094967359/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree009.table
  base := (73334966692735136359808696044838569059/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-2279422076392567143573392613844016000000000000)
      constant := (7325354953044800035232920887862755631193411328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree009.table
  base := (2344687734116664821861454205794124689967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-2280015487355272924031501536738391000000000000)
      constant := (7326574354841112100788473848395291736169314052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141190157624189934717/100000000000000000000)
  centralHi := (70595078812094967359/50000000000000000000)
  directionLo := (37438694209823335067/25000000000000000000)
  directionHi := (149754776839293340269/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree010.table
  base := (788741389077517537968141871416083949809/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-22780418006705265850002076778404119000000000000)
      constant := (71844698307203088538777749154023622914348914872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree010.table
  base := (6302827926818171079011964527338371402473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-22786352116332323654583166007347869000000000000)
      constant := (71863482708299820727950394081324445837240313823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37438694209823335067/25000000000000000000)
  centralHi := (149754776839293340269/100000000000000000000)
  directionLo := (157855395100799449801/100000000000000000000)
  directionHi := (78927697550399724901/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree011.table
  base := (757600000203268779041256291383647148763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-25046037325877427407843620032212094000000000000)
      constant := (79954668639518511507961686438436563322846478065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree011.table
  base := (1890845646929080379754915475617607048849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-25052564846467190992882818184050219000000000000)
      constant := (79981482374652640092002623669005464029877122798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157855395100799449801/100000000000000000000)
  centralHi := (78927697550399724901/50000000000000000000)
  directionLo := (82780067556556827251/50000000000000000000)
  directionHi := (165560135113113654503/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree012.table
  base := (169118569458665637871264542428045698971/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-3034628516116620996187240365113341000000000000)
      constant := (10002771927748310276103335015719368311570772690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree012.table
  base := (168553699358999286383500797259218646941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-3035419730733562036798052262305841000000000000)
      constant := (10006686254894740241614258992790592577272660990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82780067556556827251/50000000000000000000)
  centralHi := (165560135113113654503/100000000000000000000)
  directionLo := (172921921441196687641/100000000000000000000)
  directionHi := (86460960720598343821/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree013.table
  base := (-65832643906214699410514300622357062101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-29577275964221750523526706539828044000000000000)
      constant := (101902387715732016142666804918056747350274747949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree013.table
  base := (-70906143016911112187299366539791556019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-29584990306736925669482122537454919000000000000)
      constant := (101946506896377281058880463495088394106732139931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172921921441196687641/100000000000000000000)
  centralHi := (86460960720598343821/50000000000000000000)
  directionLo := (179982842213246395383/100000000000000000000)
  directionHi := (22497855276655799423/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree014.table
  base := (-192886507065160840589287505534553957427/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-31842895283393912081368249793636019000000000000)
      constant := (115479226188829307165959719096155084466499591384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree014.table
  base := (-193456189365154342659833338268995836931/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252810000000000000000000000000000000000000000
      center := (1971918)
      previous := (985959)
      next := (985959)
      square := (30192749782470109708581996865800000000000000)
      linear := (-448608493477067507151855981889539000000000000)
      constant := (1627221924803580404331251499047136879972379112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179982842213246395383/100000000000000000000)
  centralHi := (22497855276655799423/12500000000000000000)
  directionLo := (186777022321808360373/100000000000000000000)
  directionHi := (93388511160904180187/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree015.table
  base := (-111413803459166307703938141252422618791/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-3789834955840674848801088116382666000000000000)
      constant := (14519459349646701106929777318600571039523543775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree015.table
  base := (-1394716403500778396073137729327873968119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-3790823974111851149564602987873291000000000000)
      constant := (14526513338441217253441531751500115037344629518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186777022321808360373/100000000000000000000)
  centralHi := (93388511160904180187/50000000000000000000)
  directionLo := (96666292785598549103/50000000000000000000)
  directionHi := (193332585571197098207/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree016.table
  base := (-3827420014420972499314647803835431971327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-36374133921738235197051336301251969000000000000)
      constant := (147427596532539920859219798453197316547634630023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree016.table
  base := (-1915538942058991664026871539102620408257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-36383628497141527684381079067561969000000000000)
      constant := (147501593509975008540884158075599978791157379186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96666292785598549103/50000000000000000000)
  centralHi := (193332585571197098207/100000000000000000000)
  directionLo := (19967303578572445369/10000000000000000000)
  directionHi := (199673035785724453691/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree017.table
  base := (-4697234763080697724981100864747373004199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-38639753240910396754892879555059944000000000000)
      constant := (165686502042658883809565351331014824359990000751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree017.table
  base := (-4700499270966409783623858652050208365381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-38649841227276395022680731244264319000000000000)
      constant := (165771571849048946280978363473695499444351008669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19967303578572445369/10000000000000000000)
  centralHi := (199673035785724453691/100000000000000000000)
  directionLo := (41163650856613847339/20000000000000000000)
  directionHi := (25727281785383654587/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree018.table
  base := (-5417599280331589702193849555611478308743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-4545041395564728701414935867651991000000000000)
      constant := (20601211993159127720661673952894840377582604823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree018.table
  base := (-5420504772246652248671108180594142220761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-4546228217490140262331153713440741000000000000)
      constant := (20611957352371003212336422277430816619633646921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41163650856613847339/20000000000000000000)
  centralHi := (25727281785383654587/12500000000000000000)
  directionLo := (52946309109071225519/25000000000000000000)
  directionHi := (211785236436284902077/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree019.table
  base := (-6007372309636109648013977945269558546643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-43170991879254719870575966062675894000000000000)
      constant := (206566963699423029664363931277861856773394600507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree019.table
  base := (-6009951391859007583426478955676018237793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-43182266687546129699280035597669019000000000000)
      constant := (206675879078837414681463998274671867638055216857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52946309109071225519/25000000000000000000)
  centralHi := (211785236436284902077/100000000000000000000)
  directionLo := (108794323092494178153/50000000000000000000)
  directionHi := (217588646184988356307/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree020.table
  base := (-1296451637395223594075141203944602948869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-45436611198426881428417509316483869000000000000)
      constant := (229126480812056548023710012338346503711623197905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree020.table
  base := (-3242270879903132331841023681223500827871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-45448479417680997037579687774371369000000000000)
      constant := (229248175120117967696895093507475584431024241358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108794323092494178153/50000000000000000000)
  centralHi := (217588646184988356307/100000000000000000000)
  directionLo := (22324124064531400529/10000000000000000000)
  directionHi := (223241240645314005291/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree021.table
  base := (-6855390633370573283362615221957606932671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-5300247835288782554028783618921316000000000000)
      constant := (28118431654517333753409485573648752362205028431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree021.table
  base := (-6857407797044560037615529369085632082647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-5301632460868429375097704439008191000000000000)
      constant := (28133437015614283300448105193387829123068964967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22324124064531400529/10000000000000000000)
  centralHi := (223241240645314005291/100000000000000000000)
  directionLo := (7148568755700848043/3125000000000000000)
  directionHi := (228754200182427137377/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree022.table
  base := (-7137781425876330709161726462974547241407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-49967849836771204544100595824099819000000000000)
      constant := (278365410334981417776865289380116122704489263943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree022.table
  base := (-71395593726620405897603516989637404417/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-49980904877950731714178992127776069000000000000)
      constant := (278514390964539522364337399143173509380430143300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7148568755700848043/3125000000000000000)
  centralHi := (228754200182427137377/100000000000000000000)
  directionLo := (117068694232643700467/50000000000000000000)
  directionHi := (46827477693057480187/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree023.table
  base := (-917334628054124440277356604106947072431/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-52233469155943366101942139077907794000000000000)
      constant := (305008460202517735585277983338323247119393232952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree023.table
  base := (-7340240963942540997871298424177747748791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-52247117608085599052478644304478419000000000000)
      constant := (305171955208405789339137823290531183250559845759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117068694232643700467/50000000000000000000)
  centralHi := (46827477693057480187/20000000000000000000)
  directionLo := (47879911968836303431/20000000000000000000)
  directionHi := (59849889961045379289/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree024.table
  base := (-466615523880571579634628849233895796069/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-6055454275012836406642631370190641000000000000)
      constant := (36997898445924384431229495632886828401244715344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree024.table
  base := (-7467221513674675361792234535591554621947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-6057036704246718487864255164575641000000000000)
      constant := (37017742333388887217922819319260814937753512267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47879911968836303431/20000000000000000000)
  centralHi := (59849889961045379289/25000000000000000000)
  directionLo := (244548526533755253891/100000000000000000000)
  directionHi := (61137131633438813473/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree025.table
  base := (-7525829756540932466689680583170832981551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-56764707794287689217625225585523744000000000000)
      constant := (362271559095000624035108727346468518450182050999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree025.table
  base := (-188175832182660528504711322027086778723/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-56779543068355333729077948657883119000000000000)
      constant := (362465843244423996643431324829029942377774897080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244548526533755253891/100000000000000000000)
  centralHi := (61137131633438813473/25000000000000000000)
  directionLo := (249591294732155567113/100000000000000000000)
  directionHi := (124795647366077783557/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree026.table
  base := (-7524117176197511320057492422000717868859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-59030327113459850775466768839331719000000000000)
      constant := (392870014345872188270648524874998920960573669091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree026.table
  base := (-7525170377007545666743082812317703521433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-59045755798490201067377600834585469000000000000)
      constant := (393080580313943608340153809444679988496500315217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249591294732155567113/100000000000000000000)
  centralHi := (124795647366077783557/50000000000000000000)
  directionLo := (254534176452429855697/100000000000000000000)
  directionHi := (127267088226214927849/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree027.table
  base := (-186633355491149462063788836752759342893/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-6810660714736890259256479121459966000000000000)
      constant := (47196461407658407207970309834842543082760518920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree027.table
  base := (-7466254509879629637594842007196034731319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-6812440947625007600630805890143091000000000000)
      constant := (47221732937264012297706437809514443279220469959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254534176452429855697/100000000000000000000)
  centralHi := (127267088226214927849/50000000000000000000)
  directionLo := (129691441080897515731/50000000000000000000)
  directionHi := (259382882161795031463/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree028.table
  base := (-7353370911556357969962688644708218761509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252810000000000000000000000000000000000000000
      center := (1971918)
      previous := (985959)
      next := (985959)
      square := (30192749782470109708581996865800000000000000)
      linear := (-895233320447946111142955709111939000000000000)
      constant := (6450126643105486895228081144876792271490290971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree028.table
  base := (-183854349094802611559169863699196608437/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-63578181258759935743976905187990169000000000000)
      constant := (458203912340471489882909388854382303439575936520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129691441080897515731/50000000000000000000)
  centralHi := (259382882161795031463/100000000000000000000)
  directionLo := (264142598107163693863/100000000000000000000)
  directionHi := (33017824763395461733/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree029.table
  base := (-1797875075648136407171939927234006535997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-65827185070976335448991398600755644000000000000)
      constant := (492436656355001691825645549774393922718072595412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree029.table
  base := (-1438440031933764682343999640257025540017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-65844393988894803082276557364692519000000000000)
      constant := (492699655988971054598781818851627272249604729165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264142598107163693863/100000000000000000000)
  centralHi := (33017824763395461733/12500000000000000000)
  directionLo := (53763610262349587463/20000000000000000000)
  directionHi := (67204512827936984329/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree030.table
  base := (-1396495284318551366257704798706296101857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-7565867154460944111870326872729291000000000000)
      constant := (58688467045071649793765895010604773808708708885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree030.table
  base := (-6983085619955638233153435696735628994999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-7567845191003296713397356615710541000000000000)
      constant := (58719765193106455642994464858656504138866394439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53763610262349587463/20000000000000000000)
  centralHi := (67204512827936984329/25000000000000000000)
  directionLo := (273413564563443883307/100000000000000000000)
  directionHi := (68353391140860970827/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree031.table
  base := (-6728616627205342437698675115273381101331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-70358423709320658564674485108371594000000000000)
      constant := (565233473267195822491547433958268653475034820219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree031.table
  base := (-6729146321850291846577236027967043512267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-70376819449164537758875861718097219000000000000)
      constant := (565534447521845562595578877535949210030612836083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273413564563443883307/100000000000000000000)
  centralHi := (68353391140860970827/25000000000000000000)
  directionLo := (138966551608230034821/50000000000000000000)
  directionHi := (277933103216460069643/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree032.table
  base := (-200995964645802805457056545142758952273/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-72624043028492820122516028362179569000000000000)
      constant := (603544965876324607151147559550213367627476044064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree032.table
  base := (-1286466191238693094290909408458712897593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-72643032179299405097175513894799569000000000000)
      constant := (603865840536060268429111303584064832128762735285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138966551608230034821/50000000000000000000)
  centralHi := (277933103216460069643/100000000000000000000)
  directionLo := (56476063049675973887/20000000000000000000)
  directionHi := (70595078812094967359/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree033.table
  base := (-121877598980425333402133496619576919423/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-8321073594184997964484174623998616000000000000)
      constant := (71458637341328927410810115920217419969609815150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree033.table
  base := (-3047139593165277521794122420391705131787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-8323249434381585826163907341277991000000000000)
      constant := (71496569185026748500798017067974100440443065014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56476063049675973887/20000000000000000000)
  centralHi := (70595078812094967359/25000000000000000000)
  directionLo := (286758565723880943143/100000000000000000000)
  directionHi := (35844820715485117893/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree034.table
  base := (-1429006135783930160159053079916626949381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-77155281666837143238199114869795519000000000000)
      constant := (683979305610375862156597774229545303162326498676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree034.table
  base := (-285818533003823569271549215998521899449/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-77175457639569139773774818248204269000000000000)
      constant := (684341817509161944834119212259867082111242360020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286758565723880943143/100000000000000000000)
  centralHi := (35844820715485117893/12500000000000000000)
  directionLo := (58214193318214174629/20000000000000000000)
  directionHi := (145535483295535436573/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree035.table
  base := (-5299466440508131442718896332655107181749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-79420900986009304796040658123603494000000000000)
      constant := (726097589136347990821050289524692832865262450701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree035.table
  base := (-2649883122722172783613285711543861442489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-79441670369704007112074470424906619000000000000)
      constant := (726481841366622855782257289806753214969885853922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58214193318214174629/20000000000000000000)
  centralHi := (145535483295535436573/50000000000000000000)
  directionLo := (29532040256051264953/10000000000000000000)
  directionHi := (295320402560512649531/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree036.table
  base := (-484518324768021803203709705092921098231/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-9076280033909051817098022375267941000000000000)
      constant := (85497870210448563078825284792074548840899075910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree036.table
  base := (-4845442725387649323621594713787365485689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-9078653677759874938930458066845441000000000000)
      constant := (85543048995564928034224528607056600114899671529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29532040256051264953/10000000000000000000)
  centralHi := (295320402560512649531/100000000000000000000)
  directionLo := (37438694209823335067/12500000000000000000)
  directionHi := (299509553678586680537/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree037.table
  base := (-2176998794080369041387986965648153367743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-83952139624353627911723744631219444000000000000)
      constant := (814127557314553424725693268889323566710082668814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree037.table
  base := (-2177110994920518555247208243000341968187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-83974095829973741788673774778311319000000000000)
      constant := (814557141037386336461176292952281326867721552326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37438694209823335067/12500000000000000000)
  centralHi := (299509553678586680537/100000000000000000000)
  directionLo := (75910228774268765403/25000000000000000000)
  directionHi := (303640915097075061613/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree038.table
  base := (-478325209089043911727549142321946710851/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-86217758943525789469565287885027419000000000000)
      constant := (860036522913496415080674317399242363685290293592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree038.table
  base := (-3826795598164900530293227172376426806769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-86240308560108609126973426955013669000000000000)
      constant := (860489700283363313974517914407795688576763176681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75910228774268765403/25000000000000000000)
  centralHi := (303640915097075061613/100000000000000000000)
  directionLo := (76929203613302835217/25000000000000000000)
  directionHi := (307716814453211340869/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree039.table
  base := (-40794724677579234625550756761156753527/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-9831486473633105669711870126537266000000000000)
      constant := (100800742575622584431544060604081060564916291760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree039.table
  base := (-3263745446382973902478042003071239963111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-9834057921138164051697008792412891000000000000)
      constant := (100853786024796176323066283114740842722997105271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76929203613302835217/25000000000000000000)
  centralHi := (307716814453211340869/100000000000000000000)
  directionLo := (311739427203995237373/100000000000000000000)
  directionHi := (155869713601997618687/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree040.table
  base := (-2665416624724218661453965790182834366479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-90748997581870112585248374392643369000000000000)
      constant := (955637158352804106050486756919053603771054152471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree040.table
  base := (-1332780578508586724424090315447650987013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-90772734020378343803572731308418369000000000000)
      constant := (956139384008357819216177283216765731826420057274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311739427203995237373/100000000000000000000)
  centralHi := (155869713601997618687/50000000000000000000)
  directionLo := (315710790201598899603/100000000000000000000)
  directionHi := (78927697550399724901/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree041.table
  base := (-2032530054598556666542584275027532518541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-93014616901042274143089917646451344000000000000)
      constant := (1005327208137861084447370184655005547759562313509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree041.table
  base := (-2032654711292056173563409524085594990629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-93038946750513211141872383485120719000000000000)
      constant := (1005854890152829011081086542978161691185975485821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315710790201598899603/100000000000000000000)
  centralHi := (78927697550399724901/25000000000000000000)
  directionLo := (19977050859396387489/6250000000000000000)
  directionHi := (12785312550013687993/4000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree042.table
  base := (-682632655332683485434058143791290797407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-10586692913357159522325717877806591000000000000)
      constant := (117364023289300982730684994607997752009311890654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree042.table
  base := (-1365372761027326961652481892885505916601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-10589462164516453164463559517980341000000000000)
      constant := (117425552270394303488804120190375098335499013161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19977050859396387489/6250000000000000000)
  centralHi := (12785312550013687993/4000000000000000000)
  directionLo := (64701458469559678247/20000000000000000000)
  directionHi := (80876823086949597809/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree043.table
  base := (-165978605415746859259769746440208946777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-97545855539386597258773004154067294000000000000)
      constant := (1108483638573071478152044036888863429199344708292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree043.table
  base := (-664006988173969242297882346779052164659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-97571372210782945818471687838525419000000000000)
      constant := (1109064101295707380513434369490130366787993163291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64701458469559678247/20000000000000000000)
  centralHi := (80876823086949597809/25000000000000000000)
  directionLo := (81833978570352595559/25000000000000000000)
  directionHi := (327335914281410382237/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree044.table
  base := (7127687962498194410920601142269466757/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-99811474858558758816614547407875269000000000000)
      constant := (1161949053967643329587857589530283919466249439070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree044.table
  base := (71197178406220199554073802473663929737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-99837584940917813156771340015227769000000000000)
      constant := (1162556842206524047422742232693266029044345357887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81833978570352595559/25000000000000000000)
  centralHi := (327335914281410382237/100000000000000000000)
  directionLo := (66224054045245461801/20000000000000000000)
  directionHi := (165560135113113654503/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree045.table
  base := (420050908485049975957922159363116283949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-11341899353081213374939565629075916000000000000)
      constant := (135185787181580709120682124039839680628359009222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree045.table
  base := (84003322841609607376811660883197745829/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-11344866407894742277230110243547791000000000000)
      constant := (135256424721126040099054119821985248252303899310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66224054045245461801/20000000000000000000)
  centralHi := (165560135113113654503/50000000000000000000)
  directionLo := (66972372193594201587/20000000000000000000)
  directionHi := (5232216577624546999/1562500000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree046.table
  base := (1642386394831797582916160515202199361099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-104342713496903081932297633915491219000000000000)
      constant := (1272652418259351095773550694762177770695404011149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree046.table
  base := (82116369933130199344123087932331208983/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-104370010401187547833370644368632469000000000000)
      constant := (1273316730250121184743070283388364921967904896660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66972372193594201587/20000000000000000000)
  centralHi := (5232216577624546999/1562500000000000000)
  directionLo := (169281052178895449407/50000000000000000000)
  directionHi := (67712420871558179763/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree047.table
  base := (99119368062569946146548575457438313151/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-106608332816075243490139177169299194000000000000)
      constant := (1329889792041287383296288953431842087096967515025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree047.table
  base := (123896674011400850092729523784211179859/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-106636223131322415171670296545334819000000000000)
      constant := (1330583303048641436094120441544840209579981838180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169281052178895449407/50000000000000000000)
  centralHi := (67712420871558179763/20000000000000000000)
  directionLo := (342222341590111040797/100000000000000000000)
  directionHi := (171111170795055520399/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree048.table
  base := (1673386018241131047529764797043664719151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-12097105792805267227553413380345241000000000000)
      constant := (154264887204538017806631512854452225895845512578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree048.table
  base := (836682112271832709512386379070845462111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-12100270651273031389996660969115241000000000000)
      constant := (154345257784844267720678617303091759392471822916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342222341590111040797/100000000000000000000)
  centralHi := (171111170795055520399/50000000000000000000)
  directionLo := (345843842882393375283/100000000000000000000)
  directionHi := (86460960720598343821/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree049.table
  base := (2124323115088935460648683581732343726353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-111139571454419566605822263676915144000000000000)
      constant := (1448134810576507926914594787082999898489172087406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree049.table
  base := (212430439479737755932369140244377258379/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-111168648591592149848269600898739519000000000000)
      constant := (1448888595489480177836368290498957485086092888580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345843842882393375283/100000000000000000000)
  centralHi := (86460960720598343821/25000000000000000000)
  directionLo := (349427812625017793959/100000000000000000000)
  directionHi := (8735695315625444849/2500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree050.table
  base := (1295879887046254442670226059939602644181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-113405190773591728163663806930723119000000000000)
      constant := (1509142112666692599133588291206068298823101320524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree050.table
  base := (2591743700484213882782189325228001805739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-113434861321727017186569253075441869000000000000)
      constant := (1509926972984651237025984187935277947888426047578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349427812625017793959/100000000000000000000)
  centralHi := (8735695315625444849/2500000000000000000)
  directionLo := (176487697030237418397/50000000000000000000)
  directionHi := (70595078812094967359/20000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree051.table
  base := (6151318585512882430549437494638181039331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-12852312232529321080167261131614566000000000000)
      constant := (174600639928114944353903176217709489094553135309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree051.table
  base := (3075645497162578493191258468867963059223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-12855674894651320502763211694682691000000000000)
      constant := (174691368999906379229329193065855337619136751794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176487697030237418397/50000000000000000000)
  centralHi := (70595078812094967359/20000000000000000000)
  directionLo := (356487673543406609309/100000000000000000000)
  directionHi := (35648767354340660931/10000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree052.table
  base := (7151981574229386157126340428756916778723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-117936429411936051279346893438339069000000000000)
      constant := (1634925639765122174395995071831321663278885627573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree052.table
  base := (3575978951238433784400420378790838323999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-117967286781996751863168557428846569000000000000)
      constant := (1635774528843417803159909124566189888581000658098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356487673543406609309/100000000000000000000)
  centralHi := (35648767354340660931/10000000000000000000)
  directionLo := (179982842213246395383/50000000000000000000)
  directionHi := (359965684426492790767/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree053.table
  base := (8185456538613145652678542914550153316423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6390000000000000000000000000000000000000000
      center := (49842)
      previous := (24921)
      next := (24921)
      square := (763148890906150868390644990200000000000000)
      linear := (-42791758181241798802843872086916000000000000)
      constant := (605091370811350143145083117430877579219194297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree053.table
  base := (2046359059258904409302137231128449201099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6390000000000000000000000000000000000000000
      center := (49842)
      previous := (24921)
      next := (24921)
      square := (763148890906150868390644990200000000000000)
      linear := (-42802954614500398434128946103791000000000000)
      constant := (605405305582171086741279411056274816158009044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179982842213246395383/50000000000000000000)
  centralHi := (359965684426492790767/100000000000000000000)
  directionLo := (363410410611578853781/100000000000000000000)
  directionHi := (181705205305789426891/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree054.table
  base := (9251699742773111799484932762549585478249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-13607518672253374932781108882883891000000000000)
      constant := (196192638153459361975095130334425272028196502311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree054.table
  base := (1156460292219149879002204815583415449821/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-13611079138029609615529762420250141000000000000)
      constant := (196294351804650396674304035049679046601174803352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363410410611578853781/100000000000000000000)
  centralHi := (181705205305789426891/50000000000000000000)
  directionLo := (91705697450158220209/25000000000000000000)
  directionHi := (366822789800632880837/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree055.table
  base := (10350674384370371410949420417680849101491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-124733287369452535952871523199762994000000000000)
      constant := (1833021822022882256876754322727828362931820371941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree055.table
  base := (10350659467754619238283505008788009257439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-124765924972401353878067513958953619000000000000)
      constant := (1833971451487132260707664141056007809754649390489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91705697450158220209/25000000000000000000)
  centralHi := (366822789800632880837/100000000000000000000)
  directionLo := (18510185823848598263/5000000000000000000)
  directionHi := (370203716476971965261/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree056.table
  base := (717646843464188460125285369058311236783/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-126998906688624697510713066453570969000000000000)
      constant := (1901565840948323633435283999566751958504398122128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree056.table
  base := (717646044729573584565026504194270007141/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-127032137702536221216367166135655969000000000000)
      constant := (1902550303631766083420558112668223585297403921456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18510185823848598263/5000000000000000000)
  centralHi := (370203716476971965261/100000000000000000000)
  directionLo := (186777022321808360373/50000000000000000000)
  directionHi := (373554044643616720747/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree057.table
  base := (12646699017392122459021775252416352731279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-14362725111977428785394956634153216000000000000)
      constant := (219040639264848483656002262794240109003623552481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree057.table
  base := (12646688071877995657485893668261236666951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-14366483381407898728296313145817591000000000000)
      constant := (219153963998860231623908440051117164779620040489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186777022321808360373/50000000000000000000)
  centralHi := (373554044643616720747/100000000000000000000)
  directionLo := (37687459034252779397/10000000000000000000)
  directionHi := (376874590342527793971/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree058.table
  base := (692185051141975492803980632543426394107/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-131530145326969020626396152961186919000000000000)
      constant := (2042421519970164860957493892344784004490575075140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree058.table
  base := (216307682049805198824967905751409755153/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-131564563162805955892966470489060669000000000000)
      constant := (2043477529278231771325902166427663887000984480192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37687459034252779397/10000000000000000000)
  centralHi := (376874590342527793971/100000000000000000000)
  directionLo := (380166133975780506849/100000000000000000000)
  directionHi := (7603322679515610137/2000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree059.table
  base := (15073337060551405703555406784274355348109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-133795764646141182184237696214994894000000000000)
      constant := (2114733107588877366796452517655268319562693597659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree059.table
  base := (1507332903884026285460201444821937862353/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-133830775892940823231266122665763019000000000000)
      constant := (2115825830443640528235323702024326449129683797030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380166133975780506849/100000000000000000000)
  centralHi := (7603322679515610137/2000000000000000000)
  directionLo := (23964338902961465971/6250000000000000000)
  directionHi := (383429422447383455537/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree060.table
  base := (1633559160442741241158938357698784932947/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-15117931551701482638008804385422541000000000000)
      constant := (243144498707909381740731094415862120932420167330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree060.table
  base := (8167792370088592092421609492357671941949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-15121887624786187841062863871385041000000000000)
      constant := (243270061297090520588015922012967540968860733222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23964338902961465971/6250000000000000000)
  centralHi := (383429422447383455537/100000000000000000000)
  directionLo := (386665171142394196413/100000000000000000000)
  directionHi := (193332585571197098207/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree061.table
  base := (17630451589759117065903724248059020384009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-138327003284485505299920782722610844000000000000)
      constant := (2263123638866574637098980003508571346478547338559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree061.table
  base := (8815222858795096488657753692975530856713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-138363201353210557907865427019167719000000000000)
      constant := (2264291669566886539083364263117394965673575712126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386665171142394196413/100000000000000000000)
  centralHi := (193332585571197098207/50000000000000000000)
  directionLo := (9746851643954701371/2500000000000000000)
  directionHi := (389874065758188054841/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree062.table
  base := (29621728160968886733233204255533140441/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-140592622603657666857762325976418819000000000000)
      constant := (2339202539342206708166602308539696464969336570240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree062.table
  base := (18957901000898257559002932596043499077441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-140629414083345425246165079195870069000000000000)
      constant := (2340409164431918676626474949842483433962551800391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9746851643954701371/2500000000000000000)
  centralHi := (389874065758188054841/100000000000000000000)
  directionLo := (98264191000289779207/25000000000000000000)
  directionHi := (393056764001159116829/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree063.table
  base := (4063589130703340753259595801713762586287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-15873137991425536490622652136691866000000000000)
      constant := (268504130354837653889000458619618492388482464965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree063.table
  base := (20317941359507677866136229703296144510607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-15877291868164476953829414596952491000000000000)
      constant := (268642557744494189488701405829939856515050949473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98264191000289779207/25000000000000000000)
  centralHi := (393056764001159116829/100000000000000000000)
  directionLo := (198106948580372770397/50000000000000000000)
  directionHi := (79242779432149108159/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree064.table
  base := (4342112539418578989452356924102467073139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-145123861242001989973445412484034769000000000000)
      constant := (2495127526448392444002597073850960952876989605945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree064.table
  base := (339227484789985977786095307899452731709/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-145161839543615159922764383549274769000000000000)
      constant := (2496413221431341665886964559149123373134963280576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198106948580372770397/50000000000000000000)
  centralHi := (79242779432149108159/20000000000000000000)
  directionLo := (399346071571448907381/100000000000000000000)
  directionHi := (199673035785724453691/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree065.table
  base := (722992206363642658418958294210264795597/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-147389480561174151531286955737842744000000000000)
      constant := (2574973587349637128375040868459350386445142183904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree065.table
  base := (11567873733408786871518873016986940450683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-147428052273750027261064035725977119000000000000)
      constant := (2576299757894174035080656541893376686497787803066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399346071571448907381/100000000000000000000)
  centralHi := (199673035785724453691/50000000000000000000)
  directionLo := (80490773994487527999/20000000000000000000)
  directionHi := (100613467493109409999/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree066.table
  base := (24593503861443732567816458226006486973191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-16628344431149590343236499887961191000000000000)
      constant := (295119482889337151633823075490241838755446239849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree066.table
  base := (4918700236273821410083590645368717422361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-16632696111542766066595965322519941000000000000)
      constant := (295271402135407073103149678234229107919991277395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80490773994487527999/20000000000000000000)
  centralHi := (100613467493109409999/25000000000000000000)
  directionLo := (405537852773368978139/100000000000000000000)
  directionHi := (20276892638668448907/5000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree067.table
  base := (2608381783259725135060087126670310356677/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-151920719199518474646970042245458694000000000000)
      constant := (2738432794086750133695912935574917360606527378270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree067.table
  base := (815119235727726895793446112408679952101/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-151960477734019761937663340079381819000000000000)
      constant := (2739841797099704290731752663746679973888516545632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405537852773368978139/100000000000000000000)
  centralHi := (20276892638668448907/5000000000000000000)
  directionLo := (408598559234216638333/100000000000000000000)
  directionHi := (204299279617108319167/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree068.table
  base := (13803344307221652682404176354416081236561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-154186338518690636204811585499266669000000000000)
      constant := (2822045924592712065571495196042377234613292807022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree068.table
  base := (27606686659358668043961117205937259755833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-154226690464154629275962992256084169000000000000)
      constant := (2823497284549168707999365371785394944835992199183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408598559234216638333/100000000000000000000)
  centralHi := (204299279617108319167/50000000000000000000)
  directionLo := (41163650856613847339/10000000000000000000)
  directionHi := (411636508566138473391/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree069.table
  base := (29162112923028340638645394347195004606683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-17383550870873644195850347639230516000000000000)
      constant := (322990525736376049408436636829791848055002250837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree069.table
  base := (7290527813433817303547439202665750436563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-17388100354921055179362516048087391000000000000)
      constant := (323156563965230017626276695409866134905270752628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41163650856613847339/10000000000000000000)
  centralHi := (411636508566138473391/100000000000000000000)
  directionLo := (414652200959748364719/100000000000000000000)
  directionHi := (5183152511996854559/1250000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree070.table
  base := (6150017599002999885185948060075861434487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-158717577157034959320494672006882619000000000000)
      constant := (2993039210230712117385348955475568624038469375685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree070.table
  base := (6150017314007248681342604795071306715331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-158759115924424363952562296609488869000000000000)
      constant := (2994577165565840132022338132319794421549950468905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414652200959748364719/100000000000000000000)
  centralHi := (5183152511996854559/1250000000000000000)
  directionLo := (417646118546559094643/100000000000000000000)
  directionHi := (104411529636639773661/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree071.table
  base := (1618530575257377021201830905781048770583/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252810000000000000000000000000000000000000000
      center := (1971918)
      previous := (985959)
      next := (985959)
      square := (30192749782470109708581996865800000000000000)
      linear := (-2267368964453621420821636834657614000000000000)
      constant := (43386188115901055853420637044025941473132176460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree071.table
  base := (1618530514448700301647315362942037200079/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252810000000000000000000000000000000000000000
      center := (1971918)
      previous := (985959)
      next := (985959)
      square := (30192749782470109708581996865800000000000000)
      linear := (-2267962375416327201279745757551989000000000000)
      constant := (43408472535527761393127386701231553099103943980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417646118546559094643/100000000000000000000)
  centralHi := (104411529636639773661/25000000000000000000)
  directionLo := (210309363149414630659/50000000000000000000)
  directionHi := (420618726298829261319/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree072.table
  base := (6804736299360330288646671304423896684239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-18138757310597698048464195390499841000000000000)
      constant := (352117240678903135945467300820972402154039709605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree072.table
  base := (850592011476064048649835930394532561639/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-18143504598299344292129066773654841000000000000)
      constant := (352298025061567255756743644761073384182428820840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210309363149414630659/50000000000000000000)
  centralHi := (420618726298829261319/100000000000000000000)
  directionLo := (423570472872569804153/100000000000000000000)
  directionHi := (211785236436284902077/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree073.table
  base := (35709296323544357446847351657127626245321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-165514435114551443994019301768306544000000000000)
      constant := (3258946636918905376159319860288255990137915174271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree073.table
  base := (2231830964887304309893425502989292260141/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-165557754114828965967461253139595919000000000000)
      constant := (3260619189213352470198680871519101692106117569456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423570472872569804153/100000000000000000000)
  centralHi := (211785236436284902077/50000000000000000000)
  directionLo := (426501791398037790529/100000000000000000000)
  directionHi := (42650179139803779053/10000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree074.table
  base := (4678431824994821202676963590111394098633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-167780054433723605551860845022114519000000000000)
      constant := (3350093766168550634560393652340641264089883215864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree074.table
  base := (4678431730597540812611165504644526208629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-167823966844963833305760905316298269000000000000)
      constant := (3351812438520206667228151374075955300451638657432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426501791398037790529/100000000000000000000)
  centralHi := (42650179139803779053/10000000000000000000)
  directionLo := (4294131002216610207/1000000000000000000)
  directionHi := (429413100221661020701/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree075.table
  base := (7835631032052706348081061697228024629017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-18893963750321751901078043141769166000000000000)
      constant := (382499616862949407171428359406200003926182607315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree075.table
  base := (3917815451623387997827772007462449404213/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-18898908841677633404895617499222291000000000000)
      constant := (382695774598659039477095367679256265717268365070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4294131002216610207/1000000000000000000)
  centralHi := (429413100221661020701/100000000000000000000)
  directionLo := (432304803602991719103/100000000000000000000)
  directionHi := (6754762556296745611/1562500000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree076.table
  base := (20480698511747631585723726626919959909567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-172311293072067928667543931529730469000000000000)
      constant := (3536154991952105188106653780930152418169274392434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree076.table
  base := (20480698237176390573011522172614205287649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-172356392305233567982360209669702969000000000000)
      constant := (3537967786060696943329701325533859712290541720398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432304803602991719103/100000000000000000000)
  centralHi := (6754762556296745611/1562500000000000000)
  directionLo := (435177292369976712613/100000000000000000000)
  directionHi := (217588646184988356307/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree077.table
  base := (8555435872841405571074771501200762300983/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-174576912391240090225385474783538444000000000000)
      constant := (3631069085243595760915649117904902611245808684165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree077.table
  base := (42777178896052718346810084665767659740887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-174622605035368435320659861846405319000000000000)
      constant := (3632929881061107423042070825914167702119564861537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435177292369976712613/100000000000000000000)
  centralHi := (217588646184988356307/50000000000000000000)
  directionLo := (438030944535551211583/100000000000000000000)
  directionHi := (6844233508367987681/1562500000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree078.table
  base := (44625501487814727368511722965419855795631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-19649170190045805753691890893038491000000000000)
      constant := (414137647821585773435574592515507862370024851009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree078.table
  base := (2231275054438583764394233398735569488391/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-19654313085055922517662168224789741000000000000)
      constant := (414349806127338656747141268284806944113904252980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438030944535551211583/100000000000000000000)
  centralHi := (6844233508367987681/1562500000000000000)
  directionLo := (220433062939155121041/50000000000000000000)
  directionHi := (440866125878310242083/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree079.table
  base := (74410180495761356743199353241180411989/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-179108151029584413341068561291154394000000000000)
      constant := (3824664226355043239853675187173247049706292211875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree079.table
  base := (5813295308721551694519598425611785275547/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-179155030495638169997259166199810019000000000000)
      constant := (3826622907269533617549488770564918841487026905576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220433062939155121041/50000000000000000000)
  centralHi := (440866125878310242083/100000000000000000000)
  directionLo := (221841595244891485169/50000000000000000000)
  directionHi := (443683190489782970339/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree080.table
  base := (48419762838507329831857421478845409588733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-181373770348756574898910104544962369000000000000)
      constant := (3923345272243138228949484746276288691786705887083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree080.table
  base := (48419762548727042340154753514512752442461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-181421243225773037335558818376512369000000000000)
      constant := (3925353836551450005577780973483881949509347814411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221841595244891485169/50000000000000000000)
  centralHi := (443683190489782970339/100000000000000000000)
  directionLo := (22324124064531400529/5000000000000000000)
  directionHi := (446482481290628010581/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree081.table
  base := (25182850579972979182981145930061836057499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-20404376629769859606305738644307816000000000000)
      constant := (447031329701748623451646390691772983074193086122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree081.table
  base := (2014628036522528897768773776916725889003/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-20409717328434211630428718950357191000000000000)
      constant := (447260115805694437999728923038473293364421732925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22324124064531400529/5000000000000000000)
  centralHi := (446482481290628010581/100000000000000000000)
  directionLo := (112316082629470005201/25000000000000000000)
  directionHi := (89852866103576004161/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree082.table
  base := (10468835485187507191504765538821161000121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-185905008987100898014593191052578319000000000000)
      constant := (4124474310947787039721680121541120766791640945355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree082.table
  base := (52344177215634081819073964974659257369291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-185953668686042772012158122729917069000000000000)
      constant := (4126584523745821801677105698401179610424266249741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112316082629470005201/25000000000000000000)
  centralHi := (89852866103576004161/20000000000000000000)
  directionLo := (452029060185207441377/100000000000000000000)
  directionHi := (226014530092603720689/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree083.table
  base := (54355191343460647442408477678757661619487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-188170628306273059572434734306386294000000000000)
      constant := (4226922302613327432749795880178642955637809810137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree083.table
  base := (27177595582171681432858838581027417858199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-188219881416177639350457774906619419000000000000)
      constant := (4229084280510867114942832813970816397673984306498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452029060185207441377/100000000000000000000)
  centralHi := (226014530092603720689/50000000000000000000)
  directionLo := (454776982517986326891/100000000000000000000)
  directionHi := (113694245629496581723/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree084.table
  base := (56398742665949360354224988730101456420339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-21159583069493913458919586395577141000000000000)
      constant := (481180660207753891455853705113798267117015989821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree084.table
  base := (56398742513415752966497849102354637543079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-21165121571812500743195269675924641000000000000)
      constant := (481426701345025693181819271644955063056954132681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454776982517986326891/100000000000000000000)
  centralHi := (113694245629496581723/25000000000000000000)
  directionLo := (457508400364854274753/100000000000000000000)
  directionHi := (228754200182427137377/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree085.table
  base := (29237415592964225274524805844651740317499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-192701866944617382688117820814002244000000000000)
      constant := (4435585228344751949727982441601347387650520295098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree085.table
  base := (58474831056051515245159007189655276247133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252810000000000000000000000000000000000000000
      center := (1971918)
      previous := (985959)
      next := (985959)
      square := (30192749782470109708581996865800000000000000)
      linear := (-2714821223611934845451508158591889000000000000)
      constant := (62504966452925616595097971159128552538803769373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457508400364854274753/100000000000000000000)
  centralHi := (228754200182427137377/50000000000000000000)
  directionLo := (460223607587280056271/100000000000000000000)
  directionHi := (28763975474205003517/6250000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree086.table
  base := (12116691345763237116441285180153286904863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-194967486263789544245959364067810219000000000000)
      constant := (4541800161724862557392389678453446877665853733565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree086.table
  base := (12116691323649181148872248365871775601373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-195018519606582241365356731436726469000000000000)
      constant := (4544121198355999744618609108384678337687300338615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460223607587280056271/100000000000000000000)
  centralHi := (28763975474205003517/6250000000000000000)
  directionLo := (462922889428567455959/100000000000000000000)
  directionHi := (11573072235714186399/2500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree087.table
  base := (31362309573854785084149701990885282589339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-21914789509217967311533434146846466000000000000)
      constant := (516585637971825907533932019092649185654920361642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree087.table
  base := (3920288690849292020753044963788395432013/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-21920525815190789855961820401492091000000000000)
      constant := (516849561381919434362405240276285286495043851312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462922889428567455959/100000000000000000000)
  centralHi := (11573072235714186399/2500000000000000000)
  directionLo := (58200815357950613611/12500000000000000000)
  directionHi := (465606522863604908889/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree088.table
  base := (1014036223734317213773043637900135388023/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-199498724902133867361642450575426169000000000000)
      constant := (4757996968187585754756399101749897558051505399872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree088.table
  base := (8112289779861027495047770205048158379591/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-199550945066851976041956035790131169000000000000)
      constant := (4760427180180421395458355954138582522452841960328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58200815357950613611/12500000000000000000)
  centralHi := (465606522863604908889/100000000000000000000)
  directionLo := (468274776930574801869/100000000000000000000)
  directionHi := (46827477693057480187/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree089.table
  base := (33552277069331187685191789328892872400921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-201764344221306028919483993829234144000000000000)
      constant := (4867978840861620276402983804578067984699061099742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree089.table
  base := (1677613851762241792481068321026007419869/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-201817157796986843380255687966833519000000000000)
      constant := (4870464581399383778208141749176171537772051256760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468274776930574801869/100000000000000000000)
  centralHi := (46827477693057480187/10000000000000000000)
  directionLo := (235463956522873443239/50000000000000000000)
  directionHi := (470927913045746886479/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree090.table
  base := (4333957907449066015528057984053702851237/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-22669995948942021164147281898115791000000000000)
      constant := (553246262179048634673139022892408610587165696688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree090.table
  base := (4333957903823549484258142107555527539623/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-22675930058569078968728371127059541000000000000)
      constant := (553528695104179243093851220684511678461597943952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235463956522873443239/50000000000000000000)
  centralHi := (470927913045746886479/100000000000000000000)
  directionLo := (118391546325599587351/25000000000000000000)
  directionHi := (94713237060479669881/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree091.table
  base := (71614635386918418037977713423764843247367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-206295582859650352035167080336850094000000000000)
      constant := (5091709524304847232704129750713732118307954644017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree091.table
  base := (17903658834391296276019751331802057559837/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-206349583257256578056854992320238219000000000000)
      constant := (5094308203663388231172945237194916875326347931948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118391546325599587351/25000000000000000000)
  centralHi := (94713237060479669881/20000000000000000000)
  directionLo := (47618984075482799021/10000000000000000000)
  directionHi := (476189840754827990211/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree092.table
  base := (9239810084986670160044010531344533491527/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-208561202178822513593008623590658069000000000000)
      constant := (5205458334830617341298273867557428043131199041416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree092.table
  base := (73918480637908870168034013706248316538537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-208615795987391445395154644496940569000000000000)
      constant := (5208114424465877896775789285422906907519163526687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47618984075482799021/10000000000000000000)
  centralHi := (476189840754827990211/100000000000000000000)
  directionLo := (478799119688363034311/100000000000000000000)
  directionHi := (59849889961045379289/12500000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree093.table
  base := (76254862345966402175029118063269843856609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-23425202388666075016761129649385116000000000000)
      constant := (591162532343905893272157248653794381920168242351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree093.table
  base := (76254862310254674060519860983768105940403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-23431334301947368081494921852626991000000000000)
      constant := (591464102027980976115556201572974352780648033917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478799119688363034311/100000000000000000000)
  centralHi := (59849889961045379289/12500000000000000000)
  directionLo := (481394255876193790847/100000000000000000000)
  directionHi := (3760892624032763991/781250000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree094.table
  base := (15724756068252388123843678277342361601671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-213092440817166836708691710098274019000000000000)
      constant := (5436722893019699774877450088287750751246404815605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree094.table
  base := (15724756062177858993469132911591515363369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-213148221447661180071753948850345269000000000000)
      constant := (5439495684942777661160911084479502177714972749595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481394255876193790847/100000000000000000000)
  centralHi := (3760892624032763991/781250000000000000)
  directionLo := (483975476823813140217/100000000000000000000)
  directionHi := (241987738411906570109/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree095.table
  base := (81025234628861481413791652040536190527989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-215358060136338998266533253352081994000000000000)
      constant := (5554238640537990657706207963388508815880654383539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree095.table
  base := (81025234603032622083591023227397832309857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-215414434177796047410053601027047619000000000000)
      constant := (5557070724472706028469102417334217865252410132007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483975476823813140217/100000000000000000000)
  centralHi := (241987738411906570109/50000000000000000000)
  directionLo := (243271502000892122537/50000000000000000000)
  directionHi := (19461720160071369803/4000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree096.table
  base := (83459225177700658481649267513055405591443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-24180408828390128869374977400654441000000000000)
      constant := (630334448177140741442359200078881943035751800477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree096.table
  base := (83459225155738263046572437561731510847911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (15556242)
      previous := (7778121)
      next := (7778121)
      square := (238187248283930865478813530830200000000000000)
      linear := (-24186738545325657194261472578194441000000000000)
      constant := (630655781865118514338532078081655206791996521929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243271502000892122537/50000000000000000000)
  centralHi := (19461720160071369803/4000000000000000000)
  directionLo := (244548526533755253891/50000000000000000000)
  directionHi := (489097053067510507783/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree097.table
  base := (85925751961641118510769670536601116322381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-219889298774683321382216339859697944000000000000)
      constant := (5793037072141610757286758176063368216625224098331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree097.table
  base := (5370359496435526317231557779421644618111/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-219946859638065782086652905380452319000000000000)
      constant := (5795989621836122893524862144698779509862767320976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell151.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244548526533755253891/50000000000000000000)
  centralHi := (489097053067510507783/100000000000000000000)
  directionLo := (491637834076636274191/100000000000000000000)
  directionHi := (30727364629789767137/6250000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree098.table
  base := (88424814958689543059479526849474883029173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-222154918093855482940057883113505919000000000000)
      constant := (5914319756140545981692584096442431127768097105523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree098.table
  base := (17684962988563094884776050811041838739613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17949510000000000000000000000000000000000000000
      center := (140006178)
      previous := (70003089)
      next := (70003089)
      square := (2143685234555377789309321777471800000000000000)
      linear := (-222213072368200649424952557557154669000000000000)
      constant := (5917333479583551714340729078860007553187535469815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell151.Kernel098
