import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell053.Parameters
import ForestUnimodality.BinomialMassData.Q9287_19012.Batch000_049
import ForestUnimodality.BinomialMassData.Q9287_19012.Batch050_099
import ForestUnimodality.BinomialMassData.Q9287_19012.Batch100_149
import ForestUnimodality.BinomialMassData.Q9287_19012.Batch150_199
import ForestUnimodality.BinomialMassData.Q24_49.Batch000_049
import ForestUnimodality.BinomialMassData.Q24_49.Batch050_099
import ForestUnimodality.BinomialMassData.Q24_49.Batch100_149
import ForestUnimodality.BinomialMassData.Q24_49.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree000.table
  base := (70927182200105958133065087/1000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (142)
      previous := (71)
      next := (71)
      square := (750245926065253865289150780000000000000)
      linear := (21967923772206071099388769000000000000)
      constant := (709271822001059581330650870000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree000.table
  base := (70927182200105958133065087/1000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (142)
      previous := (71)
      next := (71)
      square := (750245926065253865289150780000000000000)
      linear := (21967923772206071099388769000000000000)
      constant := (709271822001059581330650870000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree001.table
  base := (202051608643376302445440610472835169050273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-2294580969460408679056113466125767000000000000)
      constant := (1304700173497223996711326016129158770437496798702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree001.table
  base := (403284382634950534749261480585897563011129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-244547633304058616350064314313000000000000)
      constant := (138384587154510529402824354934810864112817247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9997345881853220437/20000000000000000000)
  directionHi := (24993364704633051093/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree002.table
  base := (240637125049389787950125532516238010891301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-4660058733727848972692360014391237000000000000)
      constant := (778846783616008797714682170343479117955354130387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree002.table
  base := (239763264790389985997820013471383503452081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-496630264461983915087218976393000000000000)
      constant := (82478356688381210372452327622460541684063783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9997345881853220437/20000000000000000000)
  centralHi := (24993364704633051093/50000000000000000000)
  directionLo := (35345955334629085713/50000000000000000000)
  directionHi := (70691910669258171427/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree003.table
  base := (6050854622501648697965042269710896876377/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-7025536497995289266328606562656707000000000000)
      constant := (493291925163917161236647957263244924686802479975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree003.table
  base := (150558872793174173077897134625520930200013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-748712895619909213824373638473000000000000)
      constant := (52186232231723588939835904900337679058604459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35345955334629085713/50000000000000000000)
  centralHi := (70691910669258171427/100000000000000000000)
  directionLo := (86579555041046300907/100000000000000000000)
  directionHi := (21644888760261575227/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree004.table
  base := (100938795055979372686826293071010569879427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-9391014262262729559964853110922177000000000000)
      constant := (334863860924162822676472846384190412034466324549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree004.table
  base := (50204198342937683274700978255010548641639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-1000795526777834512561528300553000000000000)
      constant := (35413069969139953907023912342809236368164354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86579555041046300907/100000000000000000000)
  centralHi := (21644888760261575227/25000000000000000000)
  directionLo := (99973458818532204371/100000000000000000000)
  directionHi := (24993364704633051093/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree005.table
  base := (35705984147845414010239692429453040331467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-11756492026530169853601099659187647000000000000)
      constant := (244737393849802295631853262974575663344438280058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree005.table
  base := (71027929636829470148843852082677316413163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-1252878157935759811298682962633000000000000)
      constant := (25887489857369520255639064874398319529714909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99973458818532204371/100000000000000000000)
  centralHi := (24993364704633051093/25000000000000000000)
  directionLo := (27943431233001727621/25000000000000000000)
  directionHi := (22354744986401382097/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree006.table
  base := (6644410990367488303719370079662254570467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-14121969790797610147237346207453117000000000000)
      constant := (192138414547753593218878263486806748027669864232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree006.table
  base := (52875501696543731394916623821394565071993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-1504960789093685110035837624713000000000000)
      constant := (20336596203736273884593336745026335819693599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27943431233001727621/25000000000000000000)
  centralHi := (22354744986401382097/20000000000000000000)
  directionLo := (4897679238531021949/4000000000000000000)
  directionHi := (61220990481637774363/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree007.table
  base := (41162193418419459754103528712567358967019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-336478521531939804915787607259563000000000000)
      constant := (3283863578353949125957807357580792463644772397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree007.table
  base := (40952867376527108302787802210135459748161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-35858028984726743036183516057000000000000)
      constant := (347877363381383416185493692054948218237127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4897679238531021949/4000000000000000000)
  centralHi := (61220990481637774363/50000000000000000000)
  directionLo := (5290098194815868711/4000000000000000000)
  directionHi := (8265778429399794861/6250000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree008.table
  base := (6554920850055517502350277695745730352571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-18852925319332490734509839303984057000000000000)
      constant := (142471707479173313140894153170943120361789024385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree008.table
  base := (32612125032846201593196926424978557151581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-2009126051409535707510146948873000000000000)
      constant := (15107443399354904828340289308791645102992283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5290098194815868711/4000000000000000000)
  centralHi := (8265778429399794861/6250000000000000000)
  directionLo := (35345955334629085713/25000000000000000000)
  directionHi := (141383821338516342853/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree009.table
  base := (2655944500062168076474965420781960670869/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-21218403083599931028146085852249527000000000000)
      constant := (132200645301058626904236795860921323076068024030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree009.table
  base := (5285684372776875569077586410825134212017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-2261208682567461006247301610953000000000000)
      constant := (14032229473783120927027301846077105173609155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35345955334629085713/25000000000000000000)
  centralHi := (141383821338516342853/100000000000000000000)
  directionLo := (149960188227798306557/100000000000000000000)
  directionHi := (74980094113899153279/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree010.table
  base := (10863335596084114136060451028201799981441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-23583880847867371321782332400514997000000000000)
      constant := (127546428534040577319600181327980387413409561134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree010.table
  base := (21617443350587356715718019047352364840339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-2513291313725386304984456273033000000000000)
      constant := (13551329148936817531280748105321861140236277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149960188227798306557/100000000000000000000)
  centralHi := (74980094113899153279/50000000000000000000)
  directionLo := (158071917715803924043/100000000000000000000)
  directionHi := (39517979428950981011/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree011.table
  base := (17826866628102923826660498399706853021523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-25949358612134811615418578948780467000000000000)
      constant := (127058662128550912550453489135125020067271898101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree011.table
  base := (17733468069916389964722401374931565930671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-2765373944883311603721610935113000000000000)
      constant := (13511859976713703994964206478329527114220153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158071917715803924043/100000000000000000000)
  centralHi := (39517979428950981011/25000000000000000000)
  directionLo := (33157445189511857261/20000000000000000000)
  directionHi := (82893612973779643153/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree012.table
  base := (14593578330265516271054865090714390187133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-28314836376402251909054825497045937000000000000)
      constant := (129877425852061770120063653605009701163861898171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree012.table
  base := (14512313069393040146854008225241297025247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-3017456576041236902458765597193000000000000)
      constant := (13823207204413676274255031676713764879659721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33157445189511857261/20000000000000000000)
  centralHi := (82893612973779643153/50000000000000000000)
  directionLo := (86579555041046300907/50000000000000000000)
  directionHi := (34631822016418520363/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree013.table
  base := (11860668095054929380936471461950428444939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-30680314140669692202691072045311407000000000000)
      constant := (135466544039888043543520259792388513364781850493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree013.table
  base := (5894595128236077571774652085589190909471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-3269539207199162201195920259273000000000000)
      constant := (14428848516293747192485931048978184963897106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86579555041046300907/50000000000000000000)
  centralHi := (34631822016418520363/20000000000000000000)
  directionLo := (180229715977852698793/100000000000000000000)
  directionHi := (90114857988926349397/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree014.table
  base := (14872847301856049927246105324805522633/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-674403916427288418292394257011773000000000000)
      constant := (2928011932966840975603952273983375827793458560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree014.table
  base := (9455372153441555214222598396903560035587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-71869833435858928570062753497000000000000)
      constant := (312071232397931410176245156026324920249109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180229715977852698793/100000000000000000000)
  centralHi := (90114857988926349397/50000000000000000000)
  directionLo := (93516607667425363351/50000000000000000000)
  directionHi := (187033215334850726703/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree015.table
  base := (1498231691017869360688299168659981809179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-35411269669204572789963565141842347000000000000)
      constant := (153649362649773198962720858520569476064999336865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree015.table
  base := (3717514843268327721547587771152637163197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-3773704469515012798670229583433000000000000)
      constant := (16385123445727099366593177097130709093953142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93516607667425363351/50000000000000000000)
  centralHi := (187033215334850726703/100000000000000000000)
  directionLo := (193597770533464123561/100000000000000000000)
  directionHi := (96798885266732061781/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree016.table
  base := (5722459888918825818398456918147208571487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-37776747433472013083599811690107817000000000000)
      constant := (165816741165484854567134764258127362309048565769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree016.table
  base := (2836304474934310071176351876215432055531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-4025787100672938097407384245513000000000000)
      constant := (17690692701259257355437108578251786390094266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193597770533464123561/100000000000000000000)
  centralHi := (96798885266732061781/50000000000000000000)
  directionLo := (99973458818532204371/50000000000000000000)
  directionHi := (199946917637064408743/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree017.table
  base := (4170018150428806594557975087019303187749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-40142225197739453377236058238373287000000000000)
      constant := (179837533377545725327742911303597779926880906963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree017.table
  base := (4125758229279553256830480319468225940583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-4277869731830863396144538907593000000000000)
      constant := (19193671516138954718246314059873601497619969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99973458818532204371/50000000000000000000)
  centralHi := (199946917637064408743/100000000000000000000)
  directionLo := (103050282616786411907/50000000000000000000)
  directionHi := (41220113046714564763/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree018.table
  base := (14002352707647700165048514513866813587/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-42507702962006893670872304786638757000000000000)
      constant := (195604068284125839144370221175333485944149693800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree018.table
  base := (1380606905275504912930653270588036521523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-4529952362988788694881693569673000000000000)
      constant := (20882650436389264833511944387127393053764778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103050282616786411907/50000000000000000000)
  centralHi := (41220113046714564763/20000000000000000000)
  directionLo := (106037866003887257139/50000000000000000000)
  directionHi := (212075732007774514279/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree019.table
  base := (396766261697674807744055007037812037567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-44873180726274333964508551334904227000000000000)
      constant := (213030009453603102597932861325365672689133962916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree019.table
  base := (776145948268540990690531680317356158349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-4782034994146713993618848231753000000000000)
      constant := (22748476919589141302488006723489706324627414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106037866003887257139/50000000000000000000)
  centralHi := (212075732007774514279/100000000000000000000)
  directionLo := (217887102013103529777/100000000000000000000)
  directionHi := (108943551006551764889/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree020.table
  base := (50803247441117813643726734005998390391/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-47238658490541774258144797883169697000000000000)
      constant := (232045101456277299541124525749104980273297992170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree020.table
  base := (477275298339840449124920477454421184149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-5034117625304639292356002893833000000000000)
      constant := (24783701969946594384101664275926866466163107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217887102013103529777/100000000000000000000)
  centralHi := (108943551006551764889/50000000000000000000)
  directionLo := (223547449864013820969/100000000000000000000)
  directionHi := (22354744986401382097/10000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree021.table
  base := (-454517993396267057607891032172542386173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1336078)
      previous := (668039)
      next := (668039)
      square := (7059063918347973618505619689020000000000000)
      linear := (-144618473046091004524142986680569000000000000)
      constant := (736418674893540201952714957961217548688498243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree021.table
  base := (-240841722287754226190582747525735704649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-107881637886991114103941990937000000000000)
      constant := (550657222622412037665455513526639700134914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223547449864013820969/100000000000000000000)
  centralHi := (22354744986401382097/10000000000000000000)
  directionLo := (114533985630618567011/50000000000000000000)
  directionHi := (229067971261237134023/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree022.table
  base := (-131538768010559753188404285505049298017/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-51969614019076654845417290979700637000000000000)
      constant := (274621753431393762026845217683545671161506101210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree022.table
  base := (-1339347187033432305502827723688144310063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-5538282887620489889830312217993000000000000)
      constant := (29338919076039135306253562207910966501648391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114533985630618567011/50000000000000000000)
  centralHi := (229067971261237134023/100000000000000000000)
  directionLo := (234458543403251036647/100000000000000000000)
  directionHi := (29307317925406379581/12500000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree023.table
  base := (-2086876981706140887945079796587562718841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-54335091783344095139053537527966107000000000000)
      constant := (298095848376934508705080432678060222975799785633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree023.table
  base := (-263497624951509739869219597975398075267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-5790365518778415188567466880073000000000000)
      constant := (31849640553361126410651594543899507681467352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234458543403251036647/100000000000000000000)
  centralHi := (29307317925406379581/12500000000000000000)
  directionLo := (29965991581032671033/12500000000000000000)
  directionHi := (47945586529652273653/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree024.table
  base := (-555847930729910241758146997739185991159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-56700569547611535432689784076231577000000000000)
      constant := (322980798513436226953924915824151816300752221835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree024.table
  base := (-2797805723801214274784270271117714284531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-6042448149936340487304621542153000000000000)
      constant := (34510862591833172397958158235438624000405867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29965991581032671033/12500000000000000000)
  centralHi := (47945586529652273653/20000000000000000000)
  directionLo := (244883961926551097451/100000000000000000000)
  directionHi := (61220990481637774363/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree025.table
  base := (-3401042273768477378935903317405880133951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-59066047311878975726326030624497047000000000000)
      constant := (349248957035625120852819245549768429320141679063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree025.table
  base := (-3417357179171598690457016868510158424623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-6294530781094265786041776204233000000000000)
      constant := (37319657405342503508283564784301015660354311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244883961926551097451/100000000000000000000)
  centralHi := (61220990481637774363/25000000000000000000)
  directionLo := (15620852940395656933/6250000000000000000)
  directionHi := (249933647046330510929/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree026.table
  base := (-1979726832056540682804038650370094091331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-61431525076146416019962277172762517000000000000)
      constant := (376877188097293389337035709208897894800541302006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree026.table
  base := (-1986887763174318408487868360949159349439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-6546613412252191084778930866313000000000000)
      constant := (40273575918794605603333531320436876686284846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15620852940395656933/6250000000000000000)
  centralHi := (249933647046330510929/100000000000000000000)
  directionLo := (5097666173570603859/2000000000000000000)
  directionHi := (254883308678530192951/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree027.table
  base := (-4460480700013517368513126517839735939617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-63797002840413856313598523721027987000000000000)
      constant := (405846105787777405049868150085083373618641270921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree027.table
  base := (-4473041076541712844871427205664272857117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-6798696043410116383516085528393000000000000)
      constant := (43370566885444659905755925744433154410008869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5097666173570603859/2000000000000000000)
  centralHi := (254883308678530192951/100000000000000000000)
  directionLo := (259738665123138902721/100000000000000000000)
  directionHi := (129869332561569451361/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree028.table
  base := (-613645247804276868273708648201743630719/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-1350254706217985645045607556516193000000000000)
      constant := (8900805083585438306421002992018977473999636024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree028.table
  base := (-76877624400128531686633768057304902733/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (142)
      previous := (71)
      next := (71)
      square := (750245926065253865289150780000000000000)
      linear := (-20556206048303328519688746911000000000000)
      constant := (135886036320890899333811037532332486225088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259738665123138902721/100000000000000000000)
  centralHi := (129869332561569451361/50000000000000000000)
  directionLo := (5290098194815868711/2000000000000000000)
  directionHi := (264504909740793435551/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree029.table
  base := (-5309727768602045346299468790546528818867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-68527958368948736900871016817558927000000000000)
      constant := (467743565766865667603066109083433937647745176171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree029.table
  base := (-2659682018152535457184401617020390831307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-7302861305725966980990394852553000000000000)
      constant := (49987163342475746470533744728796011889723398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5290098194815868711/2000000000000000000)
  centralHi := (264504909740793435551/100000000000000000000)
  directionLo := (134593388019267564901/50000000000000000000)
  directionHi := (269186776038535129803/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree030.table
  base := (-1133146506893486504440371707791323160001/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-70893436133216177194507263365824397000000000000)
      constant := (500646984487288360946013855123173417764649263565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree030.table
  base := (-5674163381770705861520338392573908815593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-7554943936883892279727549514633000000000000)
      constant := (53504113348844672686285570871587149276251601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134593388019267564901/50000000000000000000)
  centralHi := (269186776038535129803/100000000000000000000)
  directionLo := (136894296366809654013/50000000000000000000)
  directionHi := (273788592733619308027/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree031.table
  base := (-5980165144802035828458302243173784385057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-73258913897483617488143509914089867000000000000)
      constant := (534840059332532222840067781865646661413302549641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree031.table
  base := (-1496884097447946738054145754425455851379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-7807026568041817578464704176713000000000000)
      constant := (57158741632789534082346290481416274571908012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136894296366809654013/50000000000000000000)
  centralHi := (273788592733619308027/100000000000000000000)
  directionLo := (69578582654834799387/25000000000000000000)
  directionHi := (278314330619339197549/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree032.table
  base := (-6255540593682108455097751545657669241589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-75624391661751057781779756462355337000000000000)
      constant := (570314673694909884356338924051515041606319960957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree032.table
  base := (-6261981397246488416235108395199158999909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-8059109199199742877201858838793000000000000)
      constant := (60950191264761116897902196607262688463031213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69578582654834799387/25000000000000000000)
  centralHi := (278314330619339197549/100000000000000000000)
  directionLo := (35345955334629085713/12500000000000000000)
  directionHi := (56553528535406537141/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree033.table
  base := (-811747064383306973451523148950136562359/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-77989869426018498075416003010620807000000000000)
      constant := (607063993361875334338699030072141450992592879736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree033.table
  base := (-3249800538693291589856208144943887661869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-8311191830357668175939013500873000000000000)
      constant := (64877741027834063019288469143792493063957866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35345955334629085713/12500000000000000000)
  centralHi := (56553528535406537141/20000000000000000000)
  directionLo := (71787974646768497481/25000000000000000000)
  directionHi := (11486075943482959597/4000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree034.table
  base := (-418578566961265868843555951447484632497/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-80355347190285938369052249558886277000000000000)
      constant := (645082260329227913565991125358673347105482469776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree034.table
  base := (-3351083101008708521033195125365639351927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-8563274461515593474676168162953000000000000)
      constant := (68940783547279138837304774033711171404578078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71787974646768497481/25000000000000000000)
  centralHi := (11486075943482959597/4000000000000000000)
  directionLo := (72867553641519871399/25000000000000000000)
  directionHi := (291470214566079485597/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree035.table
  base := (-858360794905649501129796558257861348341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-1688180101113334258422214206268403000000000000)
      constant := (13966624907050891584004383220277867324113733736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree035.table
  base := (-6871168918686626542093568470900702787201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-179905246789255485171700465817000000000000)
      constant := (1492628714622193979982528544423695080489593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72867553641519871399/25000000000000000000)
  centralHi := (291470214566079485597/100000000000000000000)
  directionLo := (73931369820357550043/25000000000000000000)
  directionHi := (295725479281430200173/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree036.table
  base := (-3502066547343452455672315515809889829843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-85086302718820818956324742655417217000000000000)
      constant := (724906979199936472356450507839722923161430948118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree036.table
  base := (-7007867308988061787702962850920896423233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-9067439723831444072150477487113000000000000)
      constant := (77471379913472470977793051991062132526831081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73931369820357550043/25000000000000000000)
  centralHi := (295725479281430200173/100000000000000000000)
  directionLo := (149960188227798306557/50000000000000000000)
  directionHi := (59984075291119322623/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree037.table
  base := (-3555034017105468473393050964964422081461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-87451780483088259249960989203682687000000000000)
      constant := (766705880954005720388107822313708109307975947386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree037.table
  base := (-3556661343543611240992900494103301962319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-9319522354989369370887632149193000000000000)
      constant := (81938138207475270315091942910701134853849166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149960188227798306557/50000000000000000000)
  centralHi := (59984075291119322623/20000000000000000000)
  directionLo := (38007175582854988509/12500000000000000000)
  directionHi := (304057404662839908073/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree038.table
  base := (-3592797669020350639319881819453978623471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-89817258247355699543597235751948157000000000000)
      constant := (809758407723166506222862051174506918880388293646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree038.table
  base := (-7188430846599500621735616831347399428029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-9571604986147294669624786811273000000000000)
      constant := (86538774641285823576140389291311841996186053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38007175582854988509/12500000000000000000)
  centralHi := (304057404662839908073/100000000000000000000)
  directionLo := (308138894733101112479/100000000000000000000)
  directionHi := (1925868092081881953/625000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree039.table
  base := (-7231478876401843606845811135202867646787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-92182736011623139837233482300213627000000000000)
      constant := (854062094278969916426690302396525223380803723131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree039.table
  base := (-723394825785075074190544884299659093727/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-9823687617305219968361941473353000000000000)
      constant := (91273029745582362655449498940204169308516390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308138894733101112479/100000000000000000000)
  centralHi := (1925868092081881953/625000000000000000)
  directionLo := (312167025107349154111/100000000000000000000)
  directionHi := (4877609767302330533/1562500000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree040.table
  base := (-1812091077618985093966938843872030431459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-94548213775890580130869728848479097000000000000)
      constant := (899614856887478244700869265094929696099791913068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree040.table
  base := (-906314255969850430604586400997857392633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-10075770248463145267099096135433000000000000)
      constant := (96140684299832071656416173651981879314615048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312167025107349154111/100000000000000000000)
  centralHi := (4877609767302330533/1562500000000000000)
  directionLo := (316143835431607848087/100000000000000000000)
  directionHi := (39517979428950981011/12500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree041.table
  base := (-7236797639835179173417313659047924900861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-96913691540158020424505975396744567000000000000)
      constant := (946414933451370164482015554282065311590475005893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree041.table
  base := (-3619334227185559624351285090497765799677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-10327852879621070565836250797513000000000000)
      constant := (101141553002384671621306996821286532661421578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316143835431607848087/100000000000000000000)
  centralHi := (39517979428950981011/12500000000000000000)
  directionLo := (160035619315234580727/50000000000000000000)
  directionHi := (64014247726093832291/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree042.table
  base := (-7197240792472810268968577977760279657899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-2026105496008682871798820856020613000000000000)
      constant := (20295119044825267818116508898688573200891798163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree042.table
  base := (-7198868332114808058924205857296900862171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-215917051240387670705579703257000000000000)
      constant := (2168887329636156405154337229702921693964803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160035619315234580727/50000000000000000000)
  centralHi := (64014247726093832291/20000000000000000000)
  directionLo := (80987757915732981437/25000000000000000000)
  directionHi := (323951031662931925749/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree043.table
  base := (-1426016947532230921905176730452622265643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-101644647068692901011778468493275507000000000000)
      constant := (1043751294352632159665854630032018413730898997295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree043.table
  base := (-3565750093868212789882316364288339566737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-10832018141936921163310560121673000000000000)
      constant := (111542330177378979743620535123802199057218418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80987757915732981437/25000000000000000000)
  centralHi := (323951031662931925749/100000000000000000000)
  directionLo := (327784905132181325929/100000000000000000000)
  directionHi := (32778490513218132593/10000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree044.table
  base := (-3517830261153782530264995398046198151483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-104010124832960341305414715041540977000000000000)
      constant := (1094285248536571784109402921886367111612589766758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree044.table
  base := (-703689114721790732745287475093296130209/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-11084100773094846462047714783753000000000000)
      constant := (116941993873794815412414474209421994273383130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327784905132181325929/100000000000000000000)
  centralHi := (32778490513218132593/10000000000000000000)
  directionLo := (33157445189511857261/10000000000000000000)
  directionHi := (331574451895118572611/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree045.table
  base := (-432140535336749758309393027988797849813/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-106375602597227781599050961589806447000000000000)
      constant := (1146061790755741345112510944956658229858728842704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree045.table
  base := (-1728829546946102180299194378306224418581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-11336183404252771760784869445833000000000000)
      constant := (122474375238230942550156050475323860097706868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33157445189511857261/10000000000000000000)
  centralHi := (331574451895118572611/100000000000000000000)
  directionLo := (167660587398010365727/50000000000000000000)
  directionHi := (67064234959204146291/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree046.table
  base := (-270643459603271071129018386506446231331/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-108741080361495221892687208138071917000000000000)
      constant := (1199080154131943295681477006121682776035661775075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree046.table
  base := (-6767015914120753525000795123513834952399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-11588266035410697059522024107913000000000000)
      constant := (128139393801280466605791736162442754611327143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167660587398010365727/50000000000000000000)
  centralHi := (67064234959204146291/20000000000000000000)
  directionLo := (6780529872616702149/2000000000000000000)
  directionHi := (339026493630835107451/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree047.table
  base := (-1647843931872685702687873484398253720427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-111106558125762662186323454686337387000000000000)
      constant := (1253339688589201285416366515625702438281457233804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree047.table
  base := (-6592183112156479971464534227698023470243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-11840348666568622358259178769993000000000000)
      constant := (133936981379369555965539866191235577949706651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6780529872616702149/2000000000000000000)
  centralHi := (339026493630835107451/100000000000000000000)
  directionLo := (342691751433637320227/100000000000000000000)
  directionHi := (85672937858409330057/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree048.table
  base := (-6390287087721378467651978834074894572059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-113472035890030102479959701234602857000000000000)
      constant := (1308839842874279189123005601938260331721223426067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree048.table
  base := (-798873534459704881508736849233552118483/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-12092431297726547656996333432073000000000000)
      constant := (139867080179129595139322148872647132986882648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342691751433637320227/100000000000000000000)
  centralHi := (85672937858409330057/25000000000000000000)
  directionLo := (86579555041046300907/25000000000000000000)
  directionHi := (346318220164185203629/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree049.table
  base := (-6162965462337656682982278839938492085029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1336078)
      previous := (668039)
      next := (668039)
      square := (7059063918347973618505619689020000000000000)
      linear := (-337718698700575926453632500824689000000000000)
      constant := (3981283234345528242807479679205584727971962139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree049.table
  base := (-6163574269268239580746991941187043447973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (142)
      previous := (71)
      next := (71)
      square := (750245926065253865289150780000000000000)
      linear := (-35989836527359979462779848671000000000000)
      constant := (425450848973785041119418526882812956552027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86579555041046300907/25000000000000000000)
  centralHi := (346318220164185203629/100000000000000000000)
  directionLo := (349907105864862715299/100000000000000000000)
  directionHi := (3499071058648627153/1000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree050.table
  base := (-2954766897839845282718293333188602756659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-118202991418564983067232194331133797000000000000)
      constant := (1423560211331241709282027944601138920050540491734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree050.table
  base := (-5910062264595934751384299386955675785073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-12596596560042398254470642756233000000000000)
      constant := (152124622874123572813951337250674203205719961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349907105864862715299/100000000000000000000)
  centralHi := (3499071058648627153/1000000000000000000)
  directionLo := (353459553346290857131/100000000000000000000)
  directionHi := (88364888336572714283/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree051.table
  base := (-1126019288080101900317220552808644485413/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-120568469182832423360868440879399267000000000000)
      constant := (1482779691950495217870293636050346460323024677345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree051.table
  base := (-2815277532471646688436796940803876504533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-12848679191200323553207797418313000000000000)
      constant := (158451989945949585166472617036856540717890362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353459553346290857131/100000000000000000000)
  centralHi := (88364888336572714283/25000000000000000000)
  directionLo := (14279066018128475389/4000000000000000000)
  directionHi := (178488325226605942363/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree052.table
  base := (-1064948398813013687655185930211332707103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-122933946947099863654504687427664737000000000000)
      constant := (1543238305308507102292223713944741852508458402195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree052.table
  base := (-66564248930127351287061461912883916619/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-13100761822358248851944952080393000000000000)
      constant := (164911712488760049844032129835286465327974640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14279066018128475389/4000000000000000000)
  centralHi := (178488325226605942363/50000000000000000000)
  directionLo := (360459431955705397587/100000000000000000000)
  directionHi := (90114857988926349397/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree053.table
  base := (-1248386424543285161810356778403946030753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-125299424711367303948140933975930207000000000000)
      constant := (1604935808579363283764999184206004687904996971556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree053.table
  base := (-624236359095483406064747908406735328261/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-13352844453516174150682106742473000000000000)
      constant := (171503765100054800673260993515515918259251816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360459431955705397587/100000000000000000000)
  centralHi := (90114857988926349397/25000000000000000000)
  directionLo := (181954441552593734833/50000000000000000000)
  directionHi := (363908883105187469667/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree054.table
  base := (-579571433500792249971937074678214015477/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-127664902475634744241777180524195677000000000000)
      constant := (1667871995490106314957350792806129601297066232808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree054.table
  base := (-4636870823985227876959277153582561423819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-13604927084674099449419261404553000000000000)
      constant := (178228126210628389961403923952593181431630083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181954441552593734833/50000000000000000000)
  centralHi := (363908883105187469667/100000000000000000000)
  directionLo := (367325942889826646177/100000000000000000000)
  directionHi := (183662971444913323089/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree055.table
  base := (-6806197777344653453931458889687431949/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-130030380239902184535413427072461147000000000000)
      constant := (1732046690775571169214928298323899095504754773125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree055.table
  base := (-1063533293933272144697096194032821353223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-13857009715832024748156416066633000000000000)
      constant := (185084777501653842931919563092226969103378044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367325942889826646177/100000000000000000000)
  centralHi := (183662971444913323089/50000000000000000000)
  directionLo := (370711507019859548741/100000000000000000000)
  directionHi := (185355753509929774371/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree056.table
  base := (-769099656191888600323452577673724186961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-2701956285799380098552034155525033000000000000)
      constant := (36682851948625240917038259467302035519370938285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree056.table
  base := (-1922861648937289814748433697980942950677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-287940660142652041773338178137000000000000)
      constant := (3919871498189117018373761335140266798690522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370711507019859548741/100000000000000000000)
  centralHi := (185355753509929774371/50000000000000000000)
  directionLo := (93516607667425363351/25000000000000000000)
  directionHi := (74813286133940290681/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree057.table
  base := (-1705742356134831236119774527646412061079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-134761335768437065122685920168992087000000000000)
      constant := (1864111032992227716853172129238152431517273074654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree057.table
  base := (-3411679740619759750573160597664892154781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-14361174978147875345630725390793000000000000)
      constant := (199194890716745012725117617536016941990910117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93516607667425363351/25000000000000000000)
  centralHi := (74813286133940290681/20000000000000000000)
  directionLo := (377391531000638318213/100000000000000000000)
  directionHi := (188695765500319159107/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree058.table
  base := (-295186626289660983272162207609785585123/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-137126813532704505416322166717257557000000000000)
      constant := (1932000445648098995638775747073813157583451486990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree058.table
  base := (-1476017633205806832952908337953836407633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-14613257609305800644367880052873000000000000)
      constant := (206448328180570735646035725997587668224363762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377391531000638318213/100000000000000000000)
  centralHi := (188695765500319159107/50000000000000000000)
  directionLo := (380687589485185268523/100000000000000000000)
  directionHi := (95171897371296317131/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree059.table
  base := (-1233335650380336173167635374027637978509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-139492291296971945709958413265523027000000000000)
      constant := (2001127891898829958441962945952601778122503249834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree059.table
  base := (-308352215544803358204459140612129781953/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-14865340240463725943105034714953000000000000)
      constant := (213834006250499760739950323546072315878320968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380687589485185268523/100000000000000000000)
  centralHi := (95171897371296317131/25000000000000000000)
  directionLo := (383955354051843025039/100000000000000000000)
  directionHi := (4799441925648037813/1250000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree060.table
  base := (-195592395459507651338862172820724142143/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-141857769061239386003594659813788497000000000000)
      constant := (2071493293874073536910233812719892681454757439590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree060.table
  base := (-78242031659494712956044502535293066511/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-15117422871621651241842189377033000000000000)
      constant := (221351916805311769220231944943239861954668175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383955354051843025039/100000000000000000000)
  centralHi := (4799441925648037813/1250000000000000000)
  directionLo := (387195541066928247123/100000000000000000000)
  directionHi := (96798885266732061781/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree061.table
  base := (-709822375529363080373728741475487981759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-144223246825506826297230906362053967000000000000)
      constant := (2143096585328410297288894156877054170635625884334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree061.table
  base := (-1419754601306874170612767973272931799583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-15369505502779576540579344039113000000000000)
      constant := (229002052939213366979821243076295384392743031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387195541066928247123/100000000000000000000)
  centralHi := (96798885266732061781/25000000000000000000)
  directionLo := (390408837168354204451/100000000000000000000)
  directionHi := (97602209292088551113/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree062.table
  base := (-857851155387363731426689128745623364201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-146588724589774266590867152910319437000000000000)
      constant := (2215937709896511976056253714971782164909817847313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree062.table
  base := (-428973138487557015760585871235425943649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-15621588133937501839316498701193000000000000)
      constant := (236784408778961302351585785336188497802656786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390408837168354204451/100000000000000000000)
  centralHi := (97602209292088551113/25000000000000000000)
  directionLo := (49199487620582381427/12500000000000000000)
  directionHi := (393595900964659051417/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree063.table
  base := (-13527901516176298501585593137409673133/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-3039881680694728711928640805277243000000000000)
      constant := (46735033053306995918967860713355702233968824420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree063.table
  base := (-270640383685493575707748750825060771971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-323952464593784227307217415577000000000000)
      constant := (4993856720993759939174094754880224574596203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49199487620582381427/12500000000000000000)
  centralHi := (393595900964659051417/100000000000000000000)
  directionLo := (198378682305595076663/50000000000000000000)
  directionHi := (396757364611190153327/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree064.table
  base := (85555493553114851800831842932158628071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-151319680118309147178139646006850377000000000000)
      constant := (2365333273650079344534066385438753157689245493508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree064.table
  base := (342150687383058422970407662791857666769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-16125753396253352436790808025353000000000000)
      constant := (252745760338237798414222833019889607179701767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198378682305595076663/50000000000000000000)
  centralHi := (396757364611190153327/100000000000000000000)
  directionLo := (79978767054825763497/20000000000000000000)
  directionHi := (199946917637064408743/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree065.table
  base := (980478090169481822071625795847712558823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-153685157882576587471775892555115847000000000000)
      constant := (2441887637259030245065568048505048406720826203201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree065.table
  base := (24510409827779851939569167487624072393/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-16377836027411277735527962687433000000000000)
      constant := (260924748191302050210445183364450202273231960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79978767054825763497/20000000000000000000)
  centralHi := (199946917637064408743/50000000000000000000)
  directionLo := (100751474122989654007/25000000000000000000)
  directionHi := (403005896491958616029/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree066.table
  base := (1644201150210880672330239698958475909809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-156050635646844027765412139103381317000000000000)
      constant := (2519679680853269072238899341074200827343539758183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree066.table
  base := (328829552329806481362210621490945665637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-16629918658569203034265117349513000000000000)
      constant := (269235939810542483231605525611424971816567455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100751474122989654007/25000000000000000000)
  centralHi := (403005896491958616029/100000000000000000000)
  directionLo := (81218821888604725213/20000000000000000000)
  directionHi := (203047054721511813033/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree067.table
  base := (2333383348806786424207783911291633830681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-158416113411111468059048385651646787000000000000)
      constant := (2598709379242110749996023810815821194570516992447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree067.table
  base := (1166668578659130224830182130465763388929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-16882001289727128333002272011593000000000000)
      constant := (277679332576921436132082608160195513684805294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81218821888604725213/20000000000000000000)
  centralHi := (203047054721511813033/50000000000000000000)
  directionLo := (409159014126974403173/100000000000000000000)
  directionHi := (204579507063487201587/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree068.table
  base := (3048018039178528748449875177566475563977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-160781591175378908352684632199912257000000000000)
      constant := (2678976710974492883706053066957124389223440640399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree068.table
  base := (121919123235220993054493486662252987677/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-17134083920885053631739426673673000000000000)
      constant := (286254924261200153702615882504032819369330275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409159014126974403173/100000000000000000000)
  centralHi := (204579507063487201587/50000000000000000000)
  directionLo := (103050282616786411907/25000000000000000000)
  directionHi := (412201130467145647629/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree069.table
  base := (3788099560677059153440835233417261735089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-163147068939646348646320878748177727000000000000)
      constant := (2760481657781876387609626222039340297373250173543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree069.table
  base := (1894032499907409769474416998960053260963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-17386166552042978930476581335753000000000000)
      constant := (294962712965723930885902277368478596537020618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103050282616786411907/25000000000000000000)
  centralHi := (412201130467145647629/100000000000000000000)
  directionLo := (103805239835059631889/25000000000000000000)
  directionHi := (415220959340238527557/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree070.table
  base := (142300721625105346400178785591895213443/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1336078)
      previous := (668039)
      next := (668039)
      square := (7059063918347973618505619689020000000000000)
      linear := (-482543867941439617900749636432779000000000000)
      constant := (8289283393890803658136717870515385046025125984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree070.table
  base := (4553593204065216965817453223558831388689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-359964269044916412841096653017000000000000)
      constant := (6200055042345787438933309572004911819720823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103805239835059631889/25000000000000000000)
  centralHi := (415220959340238527557/100000000000000000000)
  directionLo := (104554745884770578991/25000000000000000000)
  directionHi := (83643796707816463193/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree071.table
  base := (2672292263188812169572751659387133283397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-167878024468181229233593371844708667000000000000)
      constant := (2927204336688743494949350045638252230925548907878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree071.table
  base := (1336139670853120168234868679210943611757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-17890331814358829527950890659913000000000000)
      constant := (312774875213353916471233706479885414635330604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104554745884770578991/25000000000000000000)
  centralHi := (83643796707816463193/20000000000000000000)
  directionLo := (13162364646053611943/3125000000000000000)
  directionHi := (421195668673715582177/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree072.table
  base := (770122545669371605789800127653653607083/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-170243502232448669527229618392974137000000000000)
      constant := (3012422044243984336295824013016989988309136590568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree072.table
  base := (6160958023208627754317085512881533209871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-18142414445516754826688045321993000000000000)
      constant := (321879246209730668639649639876454365890985753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13162364646053611943/3125000000000000000)
  centralHi := (421195668673715582177/100000000000000000000)
  directionLo := (424151464015549028557/100000000000000000000)
  directionHi := (212075732007774514279/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree073.table
  base := (7002807628486683096953925318470120556781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-172608979996716109820865864941239607000000000000)
      constant := (3098877317151504726959060374622543175961332083147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree073.table
  base := (43767426973181362493749300745715261163/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-18394497076674680125425199984073000000000000)
      constant := (331115809066717429420623982878068853532625440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424151464015549028557/100000000000000000000)
  centralHi := (212075732007774514279/50000000000000000000)
  directionLo := (427086803288943559343/100000000000000000000)
  directionHi := (26692925205558972459/6250000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree074.table
  base := (7870063776449098779984340484748281818699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-174974457760983550114502111489505077000000000000)
      constant := (3186570147216178442133882270827767578685823639613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree074.table
  base := (7870047084656044754416678098585527265859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-18646579707832605424162354646153000000000000)
      constant := (340484562934957839732324812362646835852189637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427086803288943559343/100000000000000000000)
  centralHi := (26692925205558972459/6250000000000000000)
  directionLo := (215001052707076273831/50000000000000000000)
  directionHi := (430002105414152547663/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree075.table
  base := (8762746645622220942872178297767666518251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-177339935525250990408138358037770547000000000000)
      constant := (3275500527455382786260751913425934056674686715037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree075.table
  base := (8762732221123784333969748333871100737787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-18898662338990530722899509308233000000000000)
      constant := (349985507091090307750249114789117787553060941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215001052707076273831/50000000000000000000)
  centralHi := (430002105414152547663/100000000000000000000)
  directionLo := (86579555041046300907/20000000000000000000)
  directionHi := (54112221900653938067/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree076.table
  base := (1936170878480826858725292523965659978503/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-179705413289518430701774604586036017000000000000)
      constant := (3365668451919285264942725621010533271475215056805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree076.table
  base := (4840420964466983688784695130586217672611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-19150744970148456021636663970313000000000000)
      constant := (359618640919025687083886120120030145323411146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86579555041046300907/20000000000000000000)
  centralHi := (54112221900653938067/12500000000000000000)
  directionLo := (217887102013103529777/50000000000000000000)
  directionHi := (87154840805241411911/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree077.table
  base := (2124877089161131062113861615705707795793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-3715732470485425938681854104781663000000000000)
      constant := (70552528888527610388973023182280066162771571795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree077.table
  base := (5312187339104373740859820914067376317089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (142)
      previous := (71)
      next := (71)
      square := (750245926065253865289150780000000000000)
      linear := (-56568010499435514053567984351000000000000)
      constant := (1076921177533573983722556015660134752634178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217887102013103529777/50000000000000000000)
  centralHi := (87154840805241411911/20000000000000000000)
  directionLo := (219315885204258246907/50000000000000000000)
  directionHi := (87726354081703298763/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree078.table
  base := (181145913548258217581166315861703297703/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-184436368818053311289047097682566957000000000000)
      constant := (3549716913990593141944474707576994899934177392704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree078.table
  base := (5796664582921014760079974897462464361943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-19654910232464306619110973294473000000000000)
      constant := (379281475569095485120793524782043250552292898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219315885204258246907/50000000000000000000)
  centralHi := (87726354081703298763/20000000000000000000)
  directionLo := (11036771015811891277/2500000000000000000)
  directionHi := (441470840632475651081/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree079.table
  base := (12587712315396238864175673045347033190613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-186801846582320751582683344230832427000000000000)
      constant := (3643597443595634588808502314059852901204633856931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree079.table
  base := (12587704281854549501097525703167916315153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-19906992863622231917848127956553000000000000)
      constant := (389311175563541625646571627910658595296097479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11036771015811891277/2500000000000000000)
  centralHi := (441470840632475651081/100000000000000000000)
  directionLo := (6942058894926623937/1562500000000000000)
  directionHi := (444291769275303931969/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree080.table
  base := (13607506018484235366445005415847698763221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-189167324346588191876319590779097897000000000000)
      constant := (3738715501215265024341432064241992132198459211427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree080.table
  base := (13607499080753508501352376410058099152053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-20159075494780157216585282618633000000000000)
      constant := (399473063553050267963520285109289928009154179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6942058894926623937/1562500000000000000)
  centralHi := (444291769275303931969/100000000000000000000)
  directionLo := (447094899728027641939/100000000000000000000)
  directionHi := (22354744986401382097/5000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree081.table
  base := (3663179686947513717348113643995126547589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-191532802110855632169955837327363367000000000000)
      constant := (3835071084175475590881539416355401441881555444172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree081.table
  base := (732635637857480620183112751341076530483/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-20411158125938082515322437280713000000000000)
      constant := (409767139261372884189418545695087784999113380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447094899728027641939/100000000000000000000)
  centralHi := (22354744986401382097/5000000000000000000)
  directionLo := (449880564683394919671/100000000000000000000)
  directionHi := (56235070585424364959/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree082.table
  base := (3144669959439533716663074141830674116951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-193898279875123072463592083875628837000000000000)
      constant := (3932664190197427208224191274781440810394362209685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree082.table
  base := (15723344624996455295620260336659484393059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-20663240757096007814059591942793000000000000)
      constant := (420193402453195557096310842550690203146819237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449880564683394919671/100000000000000000000)
  centralHi := (56235070585424364959/12500000000000000000)
  directionLo := (113162271649191197237/25000000000000000000)
  directionHi := (452649086596764788949/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree083.table
  base := (8409699282473382412252741254754289027461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-196263757639390512757228330423894307000000000000)
      constant := (4031494817339066645356607823742242613845135056614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree083.table
  base := (65700758202782618984011986515101554391/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-20915323388253933112796746604873000000000000)
      constant := (430751852928075368140156647615542037287964928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113162271649191197237/25000000000000000000)
  centralHi := (452649086596764788949/100000000000000000000)
  directionLo := (56925097265222220033/12500000000000000000)
  directionHi := (91080155624355552053/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree084.table
  base := (8970432269109885973025542124466109354189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-4053657865380774552058460754533873000000000000)
      constant := (84317611509089477957778414799870189720789900214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree084.table
  base := (17940860684125533277580907433553463256833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-431987877947180783908855127897000000000000)
      constant := (9009030418679114327686917000322874242797831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56925097265222220033/12500000000000000000)
  centralHi := (91080155624355552053/20000000000000000000)
  directionLo := (114533985630618567011/25000000000000000000)
  directionHi := (91627188504494853609/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree085.table
  base := (4771936820002276176425805314482106502073/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-200994713167925393344500823520425247000000000000)
      constant := (4232868628606031633194092876967177551187022663804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree085.table
  base := (4771935988413078478707618266635048838679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-21419488650569783710271055929033000000000000)
      constant := (452265315069372853232820421504503287006667588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114533985630618567011/25000000000000000000)
  centralHi := (91627188504494853609/20000000000000000000)
  directionLo := (115213718515849663889/25000000000000000000)
  directionHi := (460854874063398655557/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree086.table
  base := (10130023208963182698469770202433217569769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-203360190932192833638137070068690717000000000000)
      constant := (4335411810119204050276370073591736122362174173406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree086.table
  base := (5065010886844022290562051245969023606091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-21671571281727709009008210591113000000000000)
      constant := (463220326466501126767814319842797500387556852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115213718515849663889/25000000000000000000)
  centralHi := (460854874063398655557/100000000000000000000)
  directionLo := (463557858379109158949/100000000000000000000)
  directionHi := (9271157167582183179/2000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree087.table
  base := (42915523269331202051157772306149549181/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-205725668696460273931773316616956187000000000000)
      constant := (4439192507460864294057241996158837146563850973500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree087.table
  base := (21457759157744694799704134386813749714183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-21923653912885634307745365253193000000000000)
      constant := (474307524601171030334136048732733116151964769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463557858379109158949/100000000000000000000)
  centralHi := (9271157167582183179/2000000000000000000)
  directionLo := (466245172824407279279/100000000000000000000)
  directionHi := (5828064660305090991/1250000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree088.table
  base := (567022316496888766611378496450899213829/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-208091146460727714225409563165221657000000000000)
      constant := (4544210719758511254712857483126571752844022076920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree088.table
  base := (11340445261422858172825134066028728659929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-22175736544043559606482519915273000000000000)
      constant := (485526909383546605764614646526159707860711294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466245172824407279279/100000000000000000000)
  centralHi := (5828064660305090991/1250000000000000000)
  directionLo := (93783417361300414659/20000000000000000000)
  directionHi := (29307317925406379581/6250000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree089.table
  base := (2991179907904030971533598379020843547421/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-210456624224995154519045809713487127000000000000)
      constant := (4650466446268823389236045648282850796877005414616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree089.table
  base := (23929437419655199229889416491459238403913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-22427819175201484905219674577353000000000000)
      constant := (496878480737130636641672477146322518772542159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93783417361300414659/20000000000000000000)
  centralHi := (29307317925406379581/6250000000000000000)
  directionLo := (235786931050117676693/50000000000000000000)
  directionHi := (471573862100235353387/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree090.table
  base := (12601700624267166689675836958008667562429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-212822101989262594812682056261752597000000000000)
      constant := (4757959686358602602441663064685800879923097600246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree090.table
  base := (25203399658285660813801756661524572751453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-22679901806359410203956829239433000000000000)
      constant := (508362238596791716420262941371622928453748379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235786931050117676693/50000000000000000000)
  centralHi := (471573862100235353387/100000000000000000000)
  directionLo := (474215753147411772131/100000000000000000000)
  directionHi := (118553938286852943033/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree091.table
  base := (26502778448669804434051492484037450957257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-4391583260276123165435067404286083000000000000)
      constant := (99320213050786336721166365512746284132397817791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree091.table
  base := (6625694269271303324914606586645630397181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-467999682398312969442734365337000000000000)
      constant := (10611799651164964236444184478258077651121068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474215753147411772131/100000000000000000000)
  centralHi := (118553938286852943033/25000000000000000000)
  directionLo := (476843007341202568579/100000000000000000000)
  directionHi := (23842150367060128429/5000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree092.table
  base := (27827570721325360538106974583486646271109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-217553057517797475399954549358283537000000000000)
      constant := (4976658705199321215620108771286298657184348551283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree092.table
  base := (2782756953846164311102741477713847697307/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-23184067068675260801431138563593000000000000)
      constant := (531726313620811100881462591641454497601763010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476843007341202568579/100000000000000000000)
  centralHi := (23842150367060128429/5000000000000000000)
  directionLo := (29965991581032671033/6250000000000000000)
  directionHi := (479455865296522736529/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree093.table
  base := (3647222243166076295018718804366697388737/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-219918535282064915693590795906549007000000000000)
      constant := (5087864483099916667987895816170641446724838932152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree093.table
  base := (29177776925324039853093405998305977361367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-23436149699833186100168293225673000000000000)
      constant := (543606630697813094041933944619522950234948881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29965991581032671033/6250000000000000000)
  centralHi := (479455865296522736529/100000000000000000000)
  directionLo := (482054561107217970073/100000000000000000000)
  directionHi := (241027280553608985037/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree094.table
  base := (30553400017529656044118409760971970181127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-222284013046332355987227042454814477000000000000)
      constant := (5200307772857422532038318184187656612229938812449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree094.table
  base := (3055339913805051973031391664584944236079/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-23688232330991111398905447887753000000000000)
      constant := (555619134103918920925308026574918358729750970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482054561107217970073/100000000000000000000)
  centralHi := (241027280553608985037/50000000000000000000)
  directionLo := (24231966129541971849/5000000000000000000)
  directionHi := (484639322590839436981/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree095.table
  base := (1597721842507120725683690564441927788851/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-224649490810599796280863289003079947000000000000)
      constant := (5313988574188527923078186557116591818657951544740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree095.table
  base := (7988609022976040783527573521987944630703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-23940314962149036697642602549833000000000000)
      constant := (567763823810063818105842359654927460033324516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24231966129541971849/5000000000000000000)
  centralHi := (484639322590839436981/100000000000000000000)
  directionLo := (487210371521730765887/100000000000000000000)
  directionHi := (7612662055027043217/1562500000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree096.table
  base := (8345222092119454868025251682531013537711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-227014968574867236574499535551345417000000000000)
      constant := (5428906886852189788405974639640591540348314880228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree096.table
  base := (33380887714830839728718328922763924463291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-24192397593306961996379757211913000000000000)
      constant := (580040699791533218878369820034716026090908813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487210371521730765887/100000000000000000000)
  centralHi := (7612662055027043217/1562500000000000000)
  directionLo := (489767923853102194903/100000000000000000000)
  directionHi := (61220990481637774363/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree097.table
  base := (34832754509011083703721883144033438131929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-24378833705934177581904111180743000000000000)
      constant := (589336030464809799985413780601689469279251647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree097.table
  base := (8708188486395607235474606555440210077087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-24444480224464887295116911873993000000000000)
      constant := (592449762027319017886612226653799968225763364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489767923853102194903/100000000000000000000)
  centralHi := (61220990481637774363/12500000000000000000)
  directionLo := (492312189928721243503/100000000000000000000)
  directionHi := (30769511870545077719/6250000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree098.table
  base := (36310035217733748618724071442754038896529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1336078)
      previous := (668039)
      next := (668039)
      square := (7059063918347973618505619689020000000000000)
      linear := (-675644093595924539830239150576899000000000000)
      constant := (16508618208127825031345765691085732251977441361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree098.table
  base := (36310034732117316074364844739435549925813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (142)
      previous := (71)
      next := (71)
      square := (750245926065253865289150780000000000000)
      linear := (-72001640978492164996659086111000000000000)
      constant := (1763822188045396330287797580947435549925813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492312189928721243503/100000000000000000000)
  centralHi := (30769511870545077719/6250000000000000000)
  directionLo := (494843374684807199983/100000000000000000000)
  directionHi := (30927710917800449999/6250000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree099.table
  base := (37812730448748528437685554885924925798071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-234111401867669557455408275196141827000000000000)
      constant := (5781086890937411807741279208583972171504079163377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree099.table
  base := (37812730030237172497796802541374187203261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-24948645486780737892591221198153000000000000)
      constant := (617664445193128962365162822664723346210718523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494843374684807199983/100000000000000000000)
  centralHi := (30927710917800449999/6250000000000000000)
  directionLo := (124340419460669464729/25000000000000000000)
  directionHi := (497361677842677858917/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree100.table
  base := (9835210040767789606476395889965285783929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-236476879631936997749044521744407297000000000000)
      constant := (5900955247166285463248944812219307664047035482492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree100.table
  base := (9835209950606274528714210261652976163327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-25200728117938663191328375860233000000000000)
      constant := (630470066095124784382570235559787883296084644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124340419460669464729/25000000000000000000)
  centralHi := (497361677842677858917/100000000000000000000)
  directionLo := (15620852940395656933/3125000000000000000)
  directionHi := (499867294092661021857/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree101.table
  base := (20447182163804370221657358175302756125533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-238842357396204438042680768292672767000000000000)
      constant := (6022061113967664672314824156544073118816206037942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree101.table
  base := (4089436401685537311954072113388479849641/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-25452810749096588490065530522313000000000000)
      constant := (643407873194642185447477354931570485884268630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15620852940395656933/3125000000000000000)
  centralHi := (499867294092661021857/100000000000000000000)
  directionLo := (502360413269750041083/100000000000000000000)
  directionHi := (125590103317437510271/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree102.table
  base := (42473302914288581129642651533177740768937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-241207835160471878336317014840938237000000000000)
      constant := (6144404491250950796602330580315162062972960383919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree102.table
  base := (2654581415409341764831729675336342263693/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-25704893380254513788802685184393000000000000)
      constant := (656477866482427530018716697356821846343147184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502360413269750041083/100000000000000000000)
  centralHi := (125590103317437510271/25000000000000000000)
  directionLo := (25242061026072595733/5000000000000000000)
  directionHi := (504841220521451914661/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree103.table
  base := (22038827949657677159376098272351902524343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-243573312924739318629953261389203707000000000000)
      constant := (6267985378939349489314729681757914477384158694882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree103.table
  base := (44077655668656712108505791735673355678511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-25956976011412439087539839846473000000000000)
      constant := (669680045950643037819927657593919960997729273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25242061026072595733/5000000000000000000)
  centralHi := (504841220521451914661/100000000000000000000)
  directionLo := (253654948234123963469/50000000000000000000)
  directionHi := (507309896468247926939/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree104.table
  base := (11426855815634422126740278181811633835521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-245938790689006758923589507937469177000000000000)
      constant := (6392803776967826491166017319920672287304548246108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree104.table
  base := (22853711531920604168426767535086603219831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-26209058642570364386276994508553000000000000)
      constant := (683014411592656496387185668501741409808804066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253654948234123963469/50000000000000000000)
  centralHi := (507309896468247926939/100000000000000000000)
  directionLo := (509766617357060385901/100000000000000000000)
  directionHi := (254883308678530192951/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree105.table
  base := (23681302493454033213421316316386303105961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-5067434050066820392188280703790503000000000000)
      constant := (133037952760844174924423501321762742162935818686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree105.table
  base := (47362604815759315509852848838724604859769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-540023291300577340510492840217000000000000)
      constant := (14213897212303306871755181569031072234018383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509766617357060385901/100000000000000000000)
  centralHi := (254883308678530192951/50000000000000000000)
  directionLo := (512211555208094468603/100000000000000000000)
  directionHi := (128052888802023617151/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree106.table
  base := (392345608464178388324110403027359061217/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-250669746217541639510862001034000117000000000000)
      constant := (6646153103833477276065786745252686222324728534875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree106.table
  base := (9808640182122864290963248878694724923591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-26713223904886214983751303832713000000000000)
      constant := (710079701376527386531150534130049453243958565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512211555208094468603/100000000000000000000)
  centralHi := (128052888802023617151/25000000000000000000)
  directionLo := (102928975591080278931/20000000000000000000)
  directionHi := (16082652436106293583/3125000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree107.table
  base := (25374605731863428236686582752142688619407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-253035223981809079804498247582265587000000000000)
      constant := (6774684032584941681345640470129218923752920317618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree107.table
  base := (25374605668388458951458009582488026010921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-26965306536044140282488458494793000000000000)
      constant := (723810625509663693096417678263002785843491806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102928975591080278931/20000000000000000000)
  centralHi := (16082652436106293583/3125000000000000000)
  directionLo := (32316671848842997837/6250000000000000000)
  directionHi := (517066749581487965393/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree108.table
  base := (52480636193784077924519147181194989969103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-255400701746076520098134494130531057000000000000)
      constant := (6904452471502717912682222979306529676592416513561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree108.table
  base := (1640019877639430139860875571790901944763/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-27217389167202065581225613156873000000000000)
      constant := (737673735798914584661944104165800939745718688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32316671848842997837/6250000000000000000)
  centralHi := (517066749581487965393/100000000000000000000)
  directionLo := (259738665123138902721/50000000000000000000)
  directionHi := (519477330246277805443/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree109.table
  base := (54237475239586725581492822922841981533561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-257766179510343960391770740678796527000000000000)
      constant := (7035458420559027944991120654210553063057501479007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree109.table
  base := (54237475145451864794687714957503690057371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-27469471798359990879962767818953000000000000)
      constant := (751669032241461631470067399134735765689678253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259738665123138902721/50000000000000000000)
  centralHi := (519477330246277805443/100000000000000000000)
  directionLo := (521876776410711307601/100000000000000000000)
  directionHi := (260938388205355653801/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree110.table
  base := (56019728593914636652789310118710436341713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-260131657274611400685406987227061997000000000000)
      constant := (7167701879730570240757426076755845005469937922631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree110.table
  base := (5601972851286369942549437666871581031857/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-27721554429517916178699922481033000000000000)
      constant := (765796514834943786354637191930249522939269510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521876776410711307601/100000000000000000000)
  centralHi := (260938388205355653801/50000000000000000000)
  directionLo := (65533155119406775621/12500000000000000000)
  directionHi := (524265240955254204969/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree111.table
  base := (57827396250727268855260459072375039518069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-262497135038878840979043233775327467000000000000)
      constant := (7301182848997850236397784904353078138661150348803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree111.table
  base := (28913698090473550840429997991418397643299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-27973637060675841477437077143113000000000000)
      constant := (780056183577388742141975435997641020783303114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65533155119406775621/12500000000000000000)
  centralHi := (524265240955254204969/100000000000000000000)
  directionLo := (52664287329356877913/10000000000000000000)
  directionHi := (526642873293568779131/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree112.table
  base := (59660478204986860352860645044681790255817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-5405359444962169005564887353542713000000000000)
      constant := (151753088333563461808767978793361272751618875071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree112.table
  base := (3728779884057171861761390670748722081/625000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-576035095751709526044372077657000000000000)
      constant := (16213225274839886682940398670067856873072000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52664287329356877913/10000000000000000000)
  centralHi := (526642873293568779131/100000000000000000000)
  directionLo := (529009819481586871101/100000000000000000000)
  directionHi := (264504909740793435551/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree113.table
  base := (61518974452507698495408797894610229784933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-267228090567413721566315726871858407000000000000)
      constant := (7571857317757339921431299331008514190651927066771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree113.table
  base := (12303794880159381061119696309712933336097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-28477802322991692074911386467273000000000000)
      constant := (808972079502879282035390596274221680671406355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529009819481586871101/100000000000000000000)
  centralHi := (264504909740793435551/50000000000000000000)
  directionLo := (53136622232221001131/10000000000000000000)
  directionHi := (531366222322210011311/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree114.table
  base := (63402884989827655067811942358732544148781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-269593568331681161859951973420123877000000000000)
      constant := (7709050817224867833421887251895531456708286987147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree114.table
  base := (15850721236329418092229486148956312970083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-28729884954149617373648541129353000000000000)
      constant := (823628306683439613574491195184320061394953876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53136622232221001131/10000000000000000000)
  centralHi := (531366222322210011311/100000000000000000000)
  directionLo := (533712221465849051949/100000000000000000000)
  directionHi := (10674244429316981039/2000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree115.table
  base := (32656104907049355509046893266821002093343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-271959046095948602153588219968389347000000000000)
      constant := (7847481826738001989739199312367684370265637300882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree115.table
  base := (65312209775789601867868015045321048928483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-28981967585307542672385695791433000000000000)
      constant := (838416720007913647036557821247465119782469669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533712221465849051949/100000000000000000000)
  centralHi := (10674244429316981039/2000000000000000000)
  directionLo := (26802397675350180049/5000000000000000000)
  directionHi := (536047953507003600981/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree116.table
  base := (67246948922993675677548976396307773107111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-274324523860216042447224466516654817000000000000)
      constant := (7987150346289231878191601416556047811147528937857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree116.table
  base := (33623474445011966530138656177442503897673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-29234050216465467971122850453513000000000000)
      constant := (853337319475550637487025690937693557673803678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26802397675350180049/5000000000000000000)
  centralHi := (536047953507003600981/100000000000000000000)
  directionLo := (107674710415414051921/20000000000000000000)
  directionHi := (269186776038535129803/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree117.table
  base := (69207102314626716583531503252068088557693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-276690001624483482740860713064920287000000000000)
      constant := (8128056375872471376188218114998452904317091368891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree117.table
  base := (17301775571563541105282455943409471480157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-29486132847623393269860005115593000000000000)
      constant := (868390105085744674902814311881453794870775404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107674710415414051921/20000000000000000000)
  centralHi := (269186776038535129803/50000000000000000000)
  directionLo := (540689147933558096381/100000000000000000000)
  directionHi := (270344573966779048191/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree118.table
  base := (17798167496871416654727610281534963964719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-279055479388750923034496959613185757000000000000)
      constant := (8270199915482840286450105292998519840495224349412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree118.table
  base := (8899083745383873237683145941428684035907/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-29738215478781318568597159777673000000000000)
      constant := (883575076838012365937130273131584308994528808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540689147933558096381/100000000000000000000)
  centralHi := (270344573966779048191/50000000000000000000)
  directionLo := (542994869045879898663/100000000000000000000)
  directionHi := (67874358630734987333/12500000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree119.table
  base := (36601825970187187101622956056974356846331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1336078)
      previous := (668039)
      next := (668039)
      square := (7059063918347973618505619689020000000000000)
      linear := (-820469262836788231277356286184989000000000000)
      constant := (24529390568852706368897025884295126947134256758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree119.table
  base := (36601825959683447470151330300803279103331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-612046900202841711578251315097000000000000)
      constant := (18344739484325996677786881641019245907446634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542994869045879898663/100000000000000000000)
  centralHi := (67874358630734987333/12500000000000000000)
  directionLo := (545290840677878477031/100000000000000000000)
  directionHi := (68161355084734809629/12500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree120.table
  base := (37620024086181808652843710337658083721283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-283786434917285803621769452709716697000000000000)
      constant := (8558199524770386504252664467742202978077216498442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree120.table
  base := (75240048154289065944642716087719189458767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-30242380741097169166071469101833000000000000)
      constant := (914341578767336569547696235411047681984357081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545290840677878477031/100000000000000000000)
  centralHi := (68161355084734809629/12500000000000000000)
  directionLo := (547577185467238616053/100000000000000000000)
  directionHi := (273788592733619308027/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree121.table
  base := (19325464670687329893641607796763414196211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-286151912681553243915405699257982167000000000000)
      constant := (8704055594442292689156311767959689806844188838228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree121.table
  base := (77301858667199253845488733164543235839757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-30494463372255094464808623763913000000000000)
      constant := (929923108943881644886881544051846329893036651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547577185467238616053/100000000000000000000)
  centralHi := (273788592733619308027/50000000000000000000)
  directionLo := (274927011750963562021/50000000000000000000)
  directionHi := (549854023501927124043/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree122.table
  base := (19847270867754248103738514163883092537173/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-288517390445820684209041945806247637000000000000)
      constant := (8851149174130536436888559516046681682760061758604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree122.table
  base := (15877816691527938427060650525565292162029/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-30746546003413019763545778425993000000000000)
      constant := (945636825261452049317027777825280476057879735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274927011750963562021/50000000000000000000)
  centralHi := (549854023501927124043/100000000000000000000)
  directionLo := (55212147239379579731/10000000000000000000)
  directionHi := (552121472393795797311/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree123.table
  base := (81501722536811485100639788946141899360877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-290882868210088124502678192354513107000000000000)
      constant := (8999480263833971574127667979836956185462666650699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree123.table
  base := (81501722525304099082433984844864009841411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-30998628634570945062282933088073000000000000)
      constant := (961482727719942728204178201387332355375603973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55212147239379579731/10000000000000000000)
  centralHi := (552121472393795797311/100000000000000000000)
  directionLo := (554379647349474945853/100000000000000000000)
  directionHi := (277189823674737472927/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree124.table
  base := (83639775879911259995009424535068400733673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-293248345974355564796314438902778577000000000000)
      constant := (9149048863551883135338981416282754706798573335151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree124.table
  base := (83639775870013036511140977965660166998901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-31250711265728870361020087750153000000000000)
      constant := (977460816319292134254054011253453437280623043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554379647349474945853/100000000000000000000)
  centralHi := (277189823674737472927/50000000000000000000)
  directionLo := (556628661238678395097/100000000000000000000)
  directionHi := (278314330619339197549/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree125.table
  base := (85803243500206525098870975360675715300019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-295613823738623005089950685451044047000000000000)
      constant := (9299854973283916790230803511808603672203452418453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree125.table
  base := (85803243491692976964780885173707061435639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-31502793896886795659757242412233000000000000)
      constant := (993571091059475047549026539465581522072424177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556628661238678395097/100000000000000000000)
  centralHi := (278314330619339197549/50000000000000000000)
  directionLo := (69858578082504319053/12500000000000000000)
  directionHi := (22354744986401382097/4000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree126.table
  base := (87992125397680654361091725701195845739737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-6081210234752866232318100653047133000000000000)
      constant := (192895889653673854729886781993692767487956298031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree126.table
  base := (21998031347589632518813875884460495510899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (142)
      previous := (71)
      next := (71)
      square := (750245926065253865289150780000000000000)
      linear := (-92579814950567699587447221791000000000000)
      constant := (2944062833645762330008274351073841982043596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69858578082504319053/12500000000000000000)
  centralHi := (22354744986401382097/4000000000000000000)
  directionLo := (280549823002276090053/50000000000000000000)
  directionHi := (561099646004552180107/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree127.table
  base := (90206421572394409968976186548665141174083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-300344779267157885677223178547574987000000000000)
      constant := (9605179722790385506957107247295736523964282802821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree127.table
  base := (90206421566097359965500668052442502149087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-32006959159202646257231551736393000000000000)
      constant := (1026188198962386497979655691514763778237136841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280549823002276090053/50000000000000000000)
  centralHi := (561099646004552180107/100000000000000000000)
  directionLo := (281660915758411961257/50000000000000000000)
  directionHi := (112664366303364784503/20000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree128.table
  base := (18489226404894510460460166719248863816819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-302710257031425325970859425095840457000000000000)
      constant := (9759698362565419303360535983533329995803951700265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree128.table
  base := (11555766502382174322217137411386147462653/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-32259041790360571555968706398473000000000000)
      constant := (1042695032125195843193661013911627588637519832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281660915758411961257/50000000000000000000)
  centralHi := (112664366303364784503/20000000000000000000)
  directionLo := (565535285354065371409/100000000000000000000)
  directionHi := (56553528535406537141/10000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree129.table
  base := (47355628377046242099071406653700195120341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-305075734795692766264495671644105927000000000000)
      constant := (9915454512355692800844600719182369081218679889734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree129.table
  base := (94711256749435986708050850307121014675021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-32511124421518496854705861060553000000000000)
      constant := (1059334051428992206843911585806214508033532203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565535285354065371409/100000000000000000000)
  centralHi := (56553528535406537141/10000000000000000000)
  directionLo := (567740109643082496937/100000000000000000000)
  directionHi := (283870054821541248469/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree130.table
  base := (12125224470184328522134852007191991648321/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-307441212559960206558131918192371397000000000000)
      constant := (10072448172161917366144465839594415641705879481016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree130.table
  base := (3880071830298829469507570348002307031879/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-32763207052676422153443015722633000000000000)
      constant := (1076105256873857085861175243995159782798362425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567740109643082496937/100000000000000000000)
  centralHi := (283870054821541248469/50000000000000000000)
  directionLo := (142484101133813900837/25000000000000000000)
  directionHi := (569936404535255603349/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree131.table
  base := (99317749046874279641864067168515816184023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-309806690324227646851768164740636867000000000000)
      constant := (10230679341984916910794603047632794982365087035601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree131.table
  base := (6207359315214483116380990498882176438663/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-33015289683834347452180170384713000000000000)
      constant := (1093008648459883119467489117043153384295382544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142484101133813900837/25000000000000000000)
  centralHi := (569936404535255603349/100000000000000000000)
  directionLo := (143031067064905892187/25000000000000000000)
  directionHi := (572124268259623568749/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree132.table
  base := (101659116610574716900541891371155544268149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-312172168088495087145404411288902337000000000000)
      constant := (10390148021825605655195942560638046481994521781763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree132.table
  base := (4066364664304599084817834090039748882099/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-33267372314992272750917325046793000000000000)
      constant := (1110044226187171839449290310245706846663998925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143031067064905892187/25000000000000000000)
  centralHi := (572124268259623568749/100000000000000000000)
  directionLo := (71787974646768497481/12500000000000000000)
  directionHi := (574303797174147979849/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree133.table
  base := (104025898452881381145138074790921411591237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-6419135629648214845694707302799343000000000000)
      constant := (215323555340509578484423953098727915931633642531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree133.table
  base := (13003237306292110081353700927151283560721/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-684070509105106082646009789977000000000000)
      constant := (23004326327670036157958036914696471879400376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71787974646768497481/12500000000000000000)
  centralHi := (574303797174147979849/100000000000000000000)
  directionLo := (144118771453808214917/25000000000000000000)
  directionHi := (576475085815232859669/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree134.table
  base := (53209047287058483525934306409226791444769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-316903123617029967732676904385433277000000000000)
      constant := (10712797911564049410750617562347932103662828423406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree134.table
  base := (21283618914385914026358615621145536756597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-33771537577308123348391634370953000000000000)
      constant := (1144511940065976836819190878632776595537563855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144118771453808214917/25000000000000000000)
  centralHi := (576475085815232859669/100000000000000000000)
  directionLo := (578638226945571993337/100000000000000000000)
  directionHi := (289319113472785996669/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree135.table
  base := (54417852487308644078108796977880868698973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-319268601381297408026313150933698747000000000000)
      constant := (10875979121463929616894965979698224462701804952502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree135.table
  base := (21767140994547395999081730429586914276771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-34023620208466048647128789033033000000000000)
      constant := (1161944076217725004197232348709821557984662265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578638226945571993337/100000000000000000000)
  centralHi := (289319113472785996669/50000000000000000000)
  directionLo := (116158662320078474137/20000000000000000000)
  directionHi := (290396655800196185343/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree136.table
  base := (22255745930945560238190790459791319873807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-321634079145564848319949397481964217000000000000)
      constant := (11040397841385724852192546608900779848707894858045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree136.table
  base := (111278729653111556286564025552981121728861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-34275702839623973945865943695113000000000000)
      constant := (1179508398511197162867464698782400524752999323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116158662320078474137/20000000000000000000)
  centralHi := (290396655800196185343/50000000000000000000)
  directionLo := (582940429132158971193/100000000000000000000)
  directionHi := (291470214566079485597/50000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree137.table
  base := (113747168614800690664397786711757732799413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-323999556909832288613585644030229687000000000000)
      constant := (11206054071330571717128662296857195182213019182531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree137.table
  base := (113747168613411498488979621096539593439779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-34527785470781899244603098357193000000000000)
      constant := (1197204906946516175252804033862569080549844197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582940429132158971193/100000000000000000000)
  centralHi := (291470214566079485597/50000000000000000000)
  directionLo := (585079667253803005023/100000000000000000000)
  directionHi := (18283739601681343907/3125000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree138.table
  base := (23248204371038485906546164027830603387281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-326365034674099728907221890578495157000000000000)
      constant := (11372947811299620652240649887665431561069639683235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree138.table
  base := (23248204370799691131895324238199150521381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-34779868101939824543340253019273000000000000)
      constant := (1215033601523806086979740019517775543144168415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (585079667253803005023/100000000000000000000)
  centralHi := (18283739601681343907/3125000000000000000)
  directionLo := (293605556040266391037/50000000000000000000)
  directionHi := (23488444483221311283/4000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree139.table
  base := (118760289376261744253007902125009804891951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-328730512438367169200858137126760627000000000000)
      constant := (11541079061294029370759918555545368023700329866937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree139.table
  base := (7422518085952225510337055067113917529851/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-35031950733097749842077407681353000000000000)
      constant := (1232994482243191468914269540094473179403822288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293605556040266391037/50000000000000000000)
  centralHi := (23488444483221311283/4000000000000000000)
  directionLo := (18416714005321362463/3125000000000000000)
  directionHi := (589334848170283598817/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree140.table
  base := (60652485589183961553837034511639765517769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-6757061024543563459071313952551553000000000000)
      constant := (238988731047244028552850112133400804752593639294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree140.table
  base := (15163121397185759563793184575187603704599/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-720082313556238268179889027417000000000000)
      constant := (25532398961322385130390474543090505807457544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18416714005321362463/3125000000000000000)
  centralHi := (589334848170283598817/100000000000000000000)
  directionLo := (118290191712572080069/20000000000000000000)
  directionHi := (295725479281430200173/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree141.table
  base := (123875067261869415735472400215833698914173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-333461467966902049788130630223291567000000000000)
      constant := (11881054091363561557089130941068327727667624638651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree141.table
  base := (123875067261111607420470678197681015789823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-35536115995413600439551717005513000000000000)
      constant := (1269312802108746373531395897823972588415909289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118290191712572080069/20000000000000000000)
  centralHi := (295725479281430200173/50000000000000000000)
  directionLo := (118711904963564896703/20000000000000000000)
  directionHi := (148389881204456120879/25000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree142.table
  base := (126470577627122679516828905622021845766761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-335826945731169490081766876771557037000000000000)
      constant := (12052897871440992235028247811415020718059072807407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree142.table
  base := (15808822203308936846036294343952713289649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-35788198626571525738288871667593000000000000)
      constant := (1287670241255163213139332476761102245266796856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118711904963564896703/20000000000000000000)
  centralHi := (148389881204456120879/25000000000000000000)
  directionLo := (148915156762793286951/25000000000000000000)
  directionHi := (119132125410234629561/20000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree143.table
  base := (6454575113724061751982332950251691589447/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-338192423495436930375403123319822507000000000000)
      constant := (12225979161548390345304578052792702118392632805780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree143.table
  base := (129091502273921699223300159470897001447259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-36040281257729451037026026329673000000000000)
      constant := (1306159866544169484722579998473021671496409837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148915156762793286951/25000000000000000000)
  centralHi := (119132125410234629561/20000000000000000000)
  directionLo := (149438585992714741413/25000000000000000000)
  directionHi := (597754343970858965653/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree144.table
  base := (131737841204294898480740687208089403837439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-340557901259704370669039369868087977000000000000)
      constant := (12400297961686884845117946502737146055842316997993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree144.table
  base := (26347568240762827179656456571124658854749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-36292363888887376335763180991753000000000000)
      constant := (1324781677975885895164822754301270789935894535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149438585992714741413/25000000000000000000)
  centralHi := (597754343970858965653/100000000000000000000)
  directionLo := (149960188227798306557/25000000000000000000)
  directionHi := (599840752911193226229/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree145.table
  base := (1680119930211364544015098315486009403879/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-342923379023971810962675616416353447000000000000)
      constant := (12575854271857590741733939251701302436481315701840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree145.table
  base := (8400599651031006490345856193583815690007/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-36544446520045301634500335653833000000000000)
      constant := (1343535675550431568040998606393547980506758416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149960188227798306557/25000000000000000000)
  centralHi := (599840752911193226229/100000000000000000000)
  directionLo := (120383985973235219763/20000000000000000000)
  directionHi := (1175624863019875193/195312500000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree146.table
  base := (68553380956332354746131694636331317301877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-345288856788239251256311862964618917000000000000)
      constant := (12752648092061607505129355796504020660542445435398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree146.table
  base := (27421352382461967032953827350337512015821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-36796529151203226933237490315913000000000000)
      constant := (1362421859267923888961309706644436833107133015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120383985973235219763/20000000000000000000)
  centralHi := (1175624863019875193/195312500000000000)
  directionLo := (603991949521794157991/100000000000000000000)
  directionHi := (75498993690224269749/12500000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree147.table
  base := (5593173747675880637002732767765301951051/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1336078)
      previous := (668039)
      next := (668039)
      square := (7059063918347973618505619689020000000000000)
      linear := (-1013569488491273153206845800329109000000000000)
      constant := (37698773825947573831002560701508473651435971475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree147.table
  base := (139829343691592144814262806672830253376449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (142)
      previous := (71)
      next := (71)
      square := (750245926065253865289150780000000000000)
      linear := (-108013445429624350530538323551000000000000)
      constant := (4027522533902269345354064458824830253376449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603991949521794157991/100000000000000000000)
  centralHi := (75498993690224269749/12500000000000000000)
  directionLo := (606056885287324106349/100000000000000000000)
  directionHi := (12121137705746482127/2000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree148.table
  base := (142577339754936066642191426555985007883553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-350019812316774131843584356061149857000000000000)
      constant := (13109948262573886650948293327079440659137488110711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree148.table
  base := (71288669877337082526993644694915079103171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-37300694413519077530711799640073000000000000)
      constant := (1400590785132208635891572409712455744264775306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (606056885287324106349/100000000000000000000)
  centralHi := (12121137705746482127/2000000000000000000)
  directionLo := (121622961865135963229/20000000000000000000)
  directionHi := (304057404662839908073/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree149.table
  base := (72675375051053064527492880156436520465857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-352385290081041572137220602609415327000000000000)
      constant := (13290454612884260489873784163191838560649388479918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree149.table
  base := (72675375050940575433353054269373908696139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-37552777044677002829448954302153000000000000)
      constant := (1419873527279226202725782496258222501365551354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121622961865135963229/20000000000000000000)
  centralHi := (304057404662839908073/50000000000000000000)
  directionLo := (305082896291419091793/50000000000000000000)
  directionHi := (610165792582838183587/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree150.table
  base := (37037393683431399121159282993840238423771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-354750767845309012430856849157680797000000000000)
      constant := (13472198473232166887436700623027094713667746557108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree150.table
  base := (37037393683383086190525094399323648656647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-37804859675834928128186108964233000000000000)
      constant := (1439288455569640586139894990937072045956919684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305082896291419091793/50000000000000000000)
  centralHi := (610165792582838183587/100000000000000000000)
  directionLo := (612209904816377743629/100000000000000000000)
  directionHi := (61220990481637774363/10000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree151.table
  base := (18871726706263360394979139448739317402951/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-357116245609576452724493095705946267000000000000)
      constant := (13655179843618614094015901141366905568047340191496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree151.table
  base := (1887172670624261139035787789036943108157/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-38056942306992853426923263626313000000000000)
      constant := (1458835570003559194657173567558221718887828080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612209904816377743629/100000000000000000000)
  centralHi := (61220990481637774363/10000000000000000000)
  directionLo := (614247214623162524457/100000000000000000000)
  directionHi := (307123607311581262229/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree152.table
  base := (7691173342577818155386165526200947603167/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-359481723373843893018129342254211737000000000000)
      constant := (13839398724044590866526343267305164185747640358580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree152.table
  base := (38455866712853447936326081602443354299937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-38309024938150778725660418288393000000000000)
      constant := (1478514870581087329893752652605528282099513564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614247214623162524457/100000000000000000000)
  centralHi := (307123607311581262229/50000000000000000000)
  directionLo := (616277789466202224959/100000000000000000000)
  directionHi := (1925868092081881953/312500000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree153.table
  base := (78349267169187172743517376417274717196117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-361847201138111333311765588802477207000000000000)
      constant := (14024855114511066388811967700856755296471409689158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree153.table
  base := (156698534338251895498776489770600405964583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-38561107569308704024397572950473000000000000)
      constant := (1498326357302328183011820051472299939245851969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616277789466202224959/100000000000000000000)
  centralHi := (1925868092081881953/312500000000000000)
  directionLo := (309150847850359235721/50000000000000000000)
  directionHi := (618301695700718471443/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree154.table
  base := (31919803222171016009388904486597064500163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-7432911814334260685824527252055973000000000000)
      constant := (290031612551407965087000956994244026795871178345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree154.table
  base := (159599016110749916110884390261153272155637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-792105922458502639247647502297000000000000)
      constant := (30985102656477200833060086469156072905089459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309150847850359235721/50000000000000000000)
  centralHi := (618301695700718471443/100000000000000000000)
  directionLo := (620318998599445647639/100000000000000000000)
  directionHi := (15507974964986141191/2500000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree155.table
  base := (162524912169286787361663661687103545580043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-366578156666646213899038081899008147000000000000)
      constant := (14399480425569292738391864675178745937804380233341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree155.table
  base := (162524912169196473006923795397982516047613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-39065272831624554621871882274633000000000000)
      constant := (1538345889176350299781001657412748003004331259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620318998599445647639/100000000000000000000)
  centralHi := (15507974964986141191/2500000000000000000)
  directionLo := (311164881188596795673/50000000000000000000)
  directionHi := (622329762377193591347/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree156.table
  base := (33095244502790341862690236371981811864869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-368943634430913654192674328447273617000000000000)
      constant := (14588649346162884611755891085921070645339687402015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree156.table
  base := (165476222513874150916083701018321253054059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-39317355462782479920609036936713000000000000)
      constant := (1558553934329327486457104138316772189797542237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311164881188596795673/50000000000000000000)
  centralHi := (622329762377193591347/100000000000000000000)
  directionLo := (624334050214698308223/100000000000000000000)
  directionHi := (4877609767302330533/781250000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree157.table
  base := (168452947145126175997109584179985156010761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-371309112195181094486310574995539087000000000000)
      constant := (14779055776800657705877791004727422323186500835407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree157.table
  base := (6738117885802382984958623042780825388983/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-39569438093940405219346191598793000000000000)
      constant := (1578894165626409283149712983549661577710529225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624334050214698308223/100000000000000000000)
  centralHi := (4877609767302330533/781250000000000000)
  directionLo := (626331924281785765413/100000000000000000000)
  directionHi := (313165962140892882707/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree158.table
  base := (171455086063080685814960726319327854597967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-373674589959448534779946821543804557000000000000)
      constant := (14970699717483484996734898532678483987381909125529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree158.table
  base := (42863771515755873954554382983649986554531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-39821520725098330518083346260873000000000000)
      constant := (1599366583067688557687691495315791781552816532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626331924281785765413/100000000000000000000)
  centralHi := (313165962140892882707/50000000000000000000)
  directionLo := (628323445759872791601/100000000000000000000)
  directionHi := (314161722879936395801/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree159.table
  base := (21810329908509999504782238185842776523253/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-376040067723715975073583068092070027000000000000)
      constant := (15163581168212220932026884909563368484239196836888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree159.table
  base := (681572809640745661938725510757787580067/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-40073603356256255816820500922953000000000000)
      constant := (1619971186653256196481453311229331811830523136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628323445759872791601/100000000000000000000)
  centralHi := (314161722879936395801/50000000000000000000)
  directionLo := (19697146089494628851/3125000000000000000)
  directionHi := (630308674863828123233/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree160.table
  base := (177535606760383221542088660824764114204741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-378405545487983415367219314640335497000000000000)
      constant := (15357700128987701749821626774318773023839475967667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree160.table
  base := (177535606760341057494311320145538371600181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-40325685987414181115557655585033000000000000)
      constant := (1640707976383201140101926032923199661458862083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19697146089494628851/3125000000000000000)
  centralHi := (630308674863828123233/100000000000000000000)
  directionLo := (25291506834528627847/4000000000000000000)
  directionHi := (39517979428950981011/6250000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree161.table
  base := (90306994270121969893632293452508170973221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 658630000000000000000000000000000000000000000
      center := (9352546)
      previous := (4676273)
      next := (4676273)
      square := (49413447428435815329539337823140000000000000)
      linear := (-7770837209229609299201133901808183000000000000)
      constant := (317409318363484608517589681541938089329618509446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree161.table
  base := (11288374283762983635219790392814277940809/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-828117726909634824781526739737000000000000)
      constant := (33909733719543069811478525247667199129370608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25291506834528627847/4000000000000000000)
  centralHi := (39517979428950981011/6250000000000000000)
  directionLo := (126852098420588277137/20000000000000000000)
  directionHi := (317130246051470692843/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree162.table
  base := (91858892303955150217016904482182533588509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-383136501016518295954491807736866437000000000000)
      constant := (15749650580682153984820260964623258661054516890166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree162.table
  base := (91858892303939609638767673739578232140437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-40829851249730031713031964909193000000000000)
      constant := (1682578114276569201183085157806006667248339782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126852098420588277137/20000000000000000000)
  centralHi := (317130246051470692843/50000000000000000000)
  directionLo := (159056799005830885709/25000000000000000000)
  directionHi := (636227196023323542837/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree163.table
  base := (18684699496362513823683790759384832262513/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-385501978780785736248128054285131907000000000000)
      constant := (15947482071602709949642883986824559235079887922310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree163.table
  base := (9342349748179922715148207185965468454301/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-41081933880887957011769119571273000000000000)
      constant := (1703711462440160814402880969891187113596504860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159056799005830885709/25000000000000000000)
  centralHi := (636227196023323542837/100000000000000000000)
  directionLo := (319093919589803430167/50000000000000000000)
  directionHi := (127637567835921372067/20000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree164.table
  base := (190001619607626088093718390895974610297109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-387867456545053176541764300833397377000000000000)
      constant := (16146551072573180627846959146718488455141926013283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree164.table
  base := (23750202450950397517456555129347235708143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-41334016512045882310506274233353000000000000)
      constant := (1724976996748466804178483519659280814783144392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319093919589803430167/50000000000000000000)
  centralHi := (127637567835921372067/20000000000000000000)
  directionLo := (160035619315234580727/25000000000000000000)
  directionHi := (640142477260938322909/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree165.table
  base := (193181658540145701314285694861510575342261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-390232934309320616835400547381662847000000000000)
      constant := (16346857583594316529250825179442379635164599475907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree165.table
  base := (193181658540126035736684887203562450519451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-41586099143203807609243428895433000000000000)
      constant := (1746374717201566965669428841298141920528171693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160035619315234580727/25000000000000000000)
  centralHi := (640142477260938322909/100000000000000000000)
  directionLo := (642091165108823255217/100000000000000000000)
  directionHi := (321045582554411627609/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree166.table
  base := (12274194485088222645715700951159112953999/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-392598412073588057129036793929928317000000000000)
      constant := (16548401604666852134136219404581351842187561131408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree166.table
  base := (196387111761394680822841176226364475196353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-41838181774361732907980583557513000000000000)
      constant := (1767904623799539386162688369850011014992349079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642091165108823255217/100000000000000000000)
  centralHi := (321045582554411627609/50000000000000000000)
  directionLo := (644033956735078771653/100000000000000000000)
  directionHi := (322016978367539385827/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree167.table
  base := (24952247408955800652337550679462577076081/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-394963889837855497422673040478193787000000000000)
      constant := (16751183135791506269282958470803788312373073777976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree167.table
  base := (49904494817907978539848150012684544161267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-42090264405519658206717738219593000000000000)
      constant := (1789566716542460485633378158452899194589258324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (644033956735078771653/100000000000000000000)
  centralHi := (322016978367539385827/50000000000000000000)
  directionLo := (645970905339301255859/100000000000000000000)
  directionHi := (32298545266965062793/5000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree168.table
  base := (101437130535534114745114000133123521502973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1336078)
      previous := (668039)
      next := (668039)
      square := (7059063918347973618505619689020000000000000)
      linear := (-1158394657732136844653962935937199000000000000)
      constant := (49432076317693826477228015629875720427642945914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree168.table
  base := (40574852214211158166440795454373124743977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (994)
      previous := (497)
      next := (497)
      square := (5251721482456777057024055460000000000000)
      linear := (-864129531360767010315405977177000000000000)
      constant := (36966550927151123611754078364999059366039195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell053.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645970905339301255859/100000000000000000000)
  centralHi := (32298545266965062793/5000000000000000000)
  directionLo := (647902063325863851497/100000000000000000000)
  directionHi := (323951031662931925749/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree169.table
  base := (206155957159890414758898617856766954420287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32272870000000000000000000000000000000000000000
      center := (458274754)
      previous := (229137377)
      next := (229137377)
      square := (2421258923993354951147427553333860000000000000)
      linear := (-399694845366390378009945533574724727000000000000)
      constant := (17160458728199969408605635090216530982030184771369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree169.table
  base := (25769494644984967274026738446321996621853/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3430000000000000000000000000000000000000000
      center := (48706)
      previous := (24353)
      next := (24353)
      square := (257334352640382075794178717540000000000000)
      linear := (-42594429667835508804192047543753000000000000)
      constant := (1833287460463446305771775353836699558730364632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell053.Kernel169
