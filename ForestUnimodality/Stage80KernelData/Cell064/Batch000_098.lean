import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell064.Parameters
import ForestUnimodality.BinomialMassData.Q9287_19012.Batch000_049
import ForestUnimodality.BinomialMassData.Q9287_19012.Batch050_099
import ForestUnimodality.BinomialMassData.Q24_49.Batch000_049
import ForestUnimodality.BinomialMassData.Q24_49.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel000
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
  base := (379011789179999216037231237/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (504406172485236115043960600000000000000)
      linear := (10250762476705596072668047500000000000)
      constant := (189505894589999608018615618500000000000000) }

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
  base := (379011789179999216037231237/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (504406172485236115043960600000000000000)
      linear := (10250762476705596072668047500000000000)
      constant := (189505894589999608018615618500000000000000) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel001
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
  base := (13742971583889051356916864543086608973093/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-10900949357009858196454108847028372500000000000)
      constant := (2486346651001623807705829964885132413099997766696) }

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
  base := (2194589664780597553703242281759205636831/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-1161751236978705206412919349152500000000000)
      constant := (263738972315589626543358099606932636701561550) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel002
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
  base := (131367967414233550907727379468766244809771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-44066947562775669608272452418283345000000000000)
      constant := (2989034558967530125779081577299593382893739948939) }

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
  base := (130891393861475637549794961973641765060991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-4696229109327961097992629360705000000000000)
      constant := (316546320717524550651254443648073877911439391) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel003
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
  base := (40706214382978975218127351931098887818803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-33165998205765811411818343571254972500000000000)
      constant := (943726213399409467460689722699256312729568942227) }

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
  base := (40504496133679636088229308728153741132103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-3534477872349255891579710011552500000000000)
      constant := (99829972125110452925282089135117132458179303) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel004
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
  base := (2054830493576556529756139668848711691/390625000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-44298522630143788019500460933368272500000000000)
      constant := (637236615071504508506813564721404425257263603200) }

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
  base := (52293139684832464376896027293949526815779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-9441682380069062468326210685505000000000000)
      constant := (134756603781149772793565982321092813884685379) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel005
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
  base := (35468419054109839999054212695638485471713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-110862094109043529254365156590963145000000000000)
      constant := (936086829238820551775900340400023229787837628417) }

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
  base := (7047374184547684838065588709130065370231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-11814409015439613153493001347905000000000000)
      constant := (99010075886343698784428881494506434769623155) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel006
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
  base := (4966746342872576198900482577697165907531/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-133127142957799482469729391315189745000000000000)
      constant := (755430560136529895682009389759123353957629943895) }

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
  base := (3082549167967607042948462767801475442329/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-7093567825405081919329896005152500000000000)
      constant := (39991839221779119436139857680405370148127716) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel007
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
  base := (8937983781877711665715206209592002834663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (17519558)
      previous := (8759779)
      next := (8759779)
      square := (232551926168765743715982638984600000000000000)
      linear := (-1585634610270973833521363531014452500000000000)
      constant := (6823630084846882546169491332044602203895864183) }

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
  base := (8871280725489417958202027661468302309619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (1862)
      previous := (931)
      next := (931)
      square := (24715902451776569637154069400000000000000)
      linear := (-168978186593680760447210027272500000000000)
      constant := (723508582804390942077012429031946813171331) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel008
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
  base := (1630793214487773710626097912510605718851/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-88828620327655694450228930381821472500000000000)
      constant := (320476935415428277895492545804977280560057642636) }

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
  base := (6469635299376609481908153908280775492327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-9466294460775632604496686667552500000000000)
      constant := (34031584322918137263190380101302141957077127) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel009
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
  base := (9490212743823582296582244277351075243039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-199922289504067342115822095487869545000000000000)
      constant := (652837444423339158698972926264904835725171236351) }

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
  base := (2350046840390202209864433229584027998671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-10652657778460907947080081998752500000000000)
      constant := (34710005240971475166426915507322502449618142) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel010
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
  base := (168290357882527871830641712170371163479/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-111093669176411647665593165106048072500000000000)
      constant := (346807090244852742219362738595332108499891206220) }

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
  base := (6652649588504000233745361966570625503987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-23678042192292366579326954659905000000000000)
      constant := (73839504798845189394657722724536071835072787) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel011
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
  base := (281355967416988272560847955459223624873/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-122226193600789624273275282468161372500000000000)
      constant := (378605187198621349299666452403049573465148534856) }

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
  base := (2215043339542561979322329067906214803947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-13025384413831458632246872661152500000000000)
      constant := (40340807792374043995660756207182821744276747) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel012
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
  base := (2645276204277360419905238020753167628389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-266717436050335201761914799660549345000000000000)
      constant := (840120352699319555002817556073577561671444554501) }

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
  base := (1289407030500748815176969976957569605431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-14211747731516733974830267992352500000000000)
      constant := (44788673090776452859668681434755124622639831) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel013
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
  base := (534965593672466611965874391229637189661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-144491242449545577488639517192387972500000000000)
      constant := (470128067251992701228285967768259281693366357949) }

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
  base := (1007344437465639819249393355828560746723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-30796222098404018634827326647105000000000000)
      constant := (100307035589672899666178496519784374352881923) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel014
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
  base := (-281808499811184575975431054108363188453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (35039116)
      previous := (17519558)
      next := (17519558)
      square := (465103852337531487431965277969200000000000000)
      linear := (-6351990484649940983523332022632705000000000000)
      constant := (21557539566299426455903150337820558627232440427) }

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
  base := (-170612021038695694109108810250205203417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (1862)
      previous := (931)
      next := (931)
      square := (24715902451776569637154069400000000000000)
      linear := (-338458660548720095101980788872500000000000)
      constant := (1150347576182914839769522426737739945032567) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel015
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
  base := (-289533464363532293017498563735975258653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-333512582596603061408007503833229145000000000000)
      constant := (1187458031713477787260086998352988627789963745615) }

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
  base := (-1504285593940496068608789270891490914891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-35541675369145120005160907971905000000000000)
      constant := (126768643296943896529221155764789530313346709) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel016
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
  base := (-2453979881643547360116497307076397900193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-355777631445359014623371738557455745000000000000)
      constant := (1333076988145717841829178415088919951349158835263) }

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
  base := (-2507990950289570846808161357626808738633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-37914402004515670690327698634305000000000000)
      constant := (142347990174797308565251469084018032218542167) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel017
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
  base := (-3320305269453438533445977442040189003719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-378042680294114967838735973281682345000000000000)
      constant := (1492734448463451854175745773051534620605283037529) }

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
  base := (-1685901595222598087549433205231308871553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-20143564319943110687747244648352500000000000)
      constant := (79712686123018588369786888587019627399401247) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel018
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
  base := (-1015499514282714154438050743953595396439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-200153864571435460527050104002954472500000000000)
      constant := (833041768697534020072152384090740135383375966098) }

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
  base := (-2055516007098886294736666261476043700081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-21329927637628386030330639979552500000000000)
      constant := (88982015460733374682635130091116019076105519) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel019
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
  base := (-4691660353726001901427151945920707856103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-422572777991626874269464442730135545000000000000)
      constant := (1852839560581594343567989629105301111786406422073) }

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
  base := (-947652663584397147454954069701083126583/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-45032581910627322745828070621505000000000000)
      constant := (197933747463890406203069869329758497065371085) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel020
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
  base := (-2609989474003146859294226436277135659569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-222418913420191413742414338727181072500000000000)
      constant := (1026380546340902447681487501432306439320455784879) }

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
  base := (-5264182884175309310662748398186047206941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-47405308545997873430994861283905000000000000)
      constant := (219308865309387652918097480621555300656134659) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel021
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
  base := (-5656222664856779210238942804600652501013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (35039116)
      previous := (17519558)
      next := (17519558)
      square := (465103852337531487431965277969200000000000000)
      linear := (-9532711748757934300003936983236505000000000000)
      constant := (46237525338557187175539623033928734320280465467) }

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
  base := (-5698065874918981744463362499772676791859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3724)
      previous := (1862)
      next := (1862)
      square := (49431804903553139274308138800000000000000)
      linear := (-1015878269007518859513503100945000000000000)
      constant := (4940145199879378694455829346431138837198909) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel022
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
  base := (-240342014137192548860822315107419324329/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-489367924537894733915557146902815345000000000000)
      constant := (2491288190669455670310089620981642554432741050975) }

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
  base := (-1512020088078396681849405671029441900461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-26075380908369487400664221304352500000000000)
      constant := (133094442200374277048582598153196619993986278) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel023
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
  base := (-15710529834059312609756237603927820091/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-255816486693325343565460690813520972500000000000)
      constant := (1364772828458296494633444264153581231819767636200) }

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
  base := (-3160742942543897369781720510701356427367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-27261744226054762743247616635552500000000000)
      constant := (145828371952423554650935534367426043217891833) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel024
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
  base := (-6489687826579289165390001222414238524237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-533898022235406640346285616351268545000000000000)
      constant := (2980264741078399067859827825283040465770815214867) }

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
  base := (-260990869109727232830685808102118451433/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-56896215087480076171662023933505000000000000)
      constant := (318455112606326939971878262474590339952734175) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel025
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
  base := (-663079182716601239286992566669723591501/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-278081535542081296780824925537747572500000000000)
      constant := (1621657051831326367642234969300174480959442927455) }

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
  base := (-6663759124623799940319776644037131335621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-59268941722850626856828814595905000000000000)
      constant := (346570013697517970125870967084666847663173979) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel026
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
  base := (-671275138718728523957889337682675145317/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-289214059966459273388507042899860872500000000000)
      constant := (1759287825629308265112885826850047361990336725735) }

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
  base := (-6743681406408944347897076456076935034233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-61641668358221177541995605258305000000000000)
      constant := (375988881951459219072377728159439278982806567) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel027
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
  base := (-6740273196970226585319807408772896590231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-600693168781674499992378320523948345000000000000)
      constant := (3805943054982750297126035669418729460424022166921) }

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
  base := (-676924958983673786941142859867786667827/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-32007197496795864113581197960352500000000000)
      constant := (203350203108481225752691455905467221052736865) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel028
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
  base := (-3358799303488384010540857843712204213261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (17519558)
      previous := (8759779)
      next := (8759779)
      square := (232551926168765743715982638984600000000000000)
      linear := (-6356716506432963808242270971920152500000000000)
      constant := (41891025494373432502610653930445514157313935299) }

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
  base := (-6744707919995954988222233278033866963749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3724)
      previous := (1862)
      next := (1862)
      square := (49431804903553139274308138800000000000000)
      linear := (-1354839216917597528823044624145000000000000)
      constant := (8952946858399377956945726492736340518776299) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel029
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
  base := (-831068947543601624270844282744240293381/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-322611633239593203211553394986200772500000000000)
      constant := (2208310797235200192780031659894402028211268754284) }

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
  base := (-6673881988036188563404386798238718768777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-68759848264332829597495977245505000000000000)
      constant := (471961666240930251772611961132748836236166423) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel030
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
  base := (-3268290417673547602092437647853253393091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-333744157663971179819235512348314072500000000000)
      constant := (2369884216511447799342100823711231278167400681181) }

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
  base := (-6560221051164859652918696673516533560707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-71132574899703380282662767907905000000000000)
      constant := (506493935088489629192033101935286802920742493) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel031
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
  base := (-3192398627003748897216074244914774894569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-344876682088349156426917629710427372500000000000)
      constant := (2537345368071005725107554633900693966748817669879) }

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
  base := (-3203417807120786430177799090870533769583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-36752650767536965483914779285152500000000000)
      constant := (271141867141039870747691692724759848419231217) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel032
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
  base := (-1549001824522653612847132427520952607411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-356009206512727133034599747072540672500000000000)
      constant := (2710662551512428106168087159821288043914809264602) }

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
  base := (-97133296963587103654741142825556891291/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-37939014085222240826498174616352500000000000)
      constant := (289662164114102196980281301485306812928329888) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel033
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
  base := (-5972742975051445009419489531936007677387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-734283461874210219284563728869307945000000000000)
      constant := (5779614333068225916694247947886423191886081186517) }

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
  base := (-599183748679600123406789251736408466259/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-39125377402907516169081569947552500000000000)
      constant := (308804820884684556213048295243924416362560705) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel034
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
  base := (-285864438737990337511617402450739074889/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-378274255361483086249963981796767272500000000000)
      constant := (3074753408670455556124962274465941898775309269990) }

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
  base := (-2867518657350822466620616111002005398489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-40311740720592791511664965278752500000000000)
      constant := (328567097603161457322985770779844185038227911) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel035
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
  base := (-1086341183761598128016672085820606620057/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (35039116)
      previous := (17519558)
      next := (17519558)
      square := (465103852337531487431965277969200000000000000)
      linear := (-15894154276973920932965146904444105000000000000)
      constant := (133284816138109578764365109509740364766411503315) }

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
  base := (-2724094550384096483825230948891025180141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (1862)
      previous := (931)
      next := (931)
      square := (24715902451776569637154069400000000000000)
      linear := (-846900082413838099066293073672500000000000)
      constant := (7121357610338146628224555163604339766173091) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel036
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
  base := (-2558927105065803240642298858468947107213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-400539304210239039465328216520993872500000000000)
      constant := (3461959919261372035420812590621154737180427152083) }

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
  base := (-2566574876991280480830436422807992275747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-42684467355963342196831755941152500000000000)
      constant := (369940867575668946386050059747478010545931453) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel037
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
  base := (-2388705865600167311421599972067447282713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-411671828634617016073010333883107172500000000000)
      constant := (3664180225515429977710792776604245941704205072583) }

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
  base := (-4791594258748793671387032914395848898239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-87741661347297235078830302544705000000000000)
      constant := (783096241583367372804821604539695566795328161) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel038
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
  base := (-4411892608549569371654647521851798871693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-845608706117989985361384902490440945000000000000)
      constant := (7744243622645528781588146921848036337523393591763) }

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
  base := (-55312918831913109175628979762565707261/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-45057193991333892881998546603552500000000000)
      constant := (413766468729384272588601168363323189474653560) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel039
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
  base := (-4022663036728242310333138082664530226389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-867873754966745938576749137214667545000000000000)
      constant := (8171538489653399885018087704915641464924874063499) }

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
  base := (-2017415188038801032489310213868135089759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-46243557309019168224581941934752500000000000)
      constant := (436594275252912632708270024663562607649488641) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel040
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
  base := (-3610955733997585419757443738163730561123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-890138803815501891792113371938894145000000000000)
      constant := (8610217203705139309680287733729414069420095256893) }

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
  base := (-3622214235509964208291883246338855404779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-94859841253408887134330674531905000000000000)
      constant := (920060129011519320706402756336740408173125621) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel041
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
  base := (-3177882984247903232603819625883221515841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-912403852664257845007477606663120745000000000000)
      constant := (9060254637185370630864316934391031348536642326431) }

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
  base := (-398536752849214727511739807692294614497/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-48616283944389718909748732597152500000000000)
      constant := (484072505207924084544742603022263202522370812) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel042
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
  base := (-2724448403943141738965497952184593818783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (35039116)
      previous := (17519558)
      next := (17519558)
      square := (465103852337531487431965277969200000000000000)
      linear := (-19074875541081914249445751865047905000000000000)
      constant := (194318941171133148908825820148724260181194466897) }

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
  base := (-2734070043774060163135260730628774953123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3724)
      previous := (1862)
      next := (1862)
      square := (49431804903553139274308138800000000000000)
      linear := (-2032761112737754867442127670545000000000000)
      constant := (20764097816009744733427007443639190027296973) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel043
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
  base := (-1125778779515352415171925799107893240943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-478466975180884875719103038055786972500000000000)
      constant := (4997158593328566205922594977074208624947817518513) }

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
  base := (-1130222307093564113605718633216832112447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-50989010579760269594915523259552500000000000)
      constant := (533972655128662412169609085790066386098014753) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel044
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
  base := (-1760027544377161039308830661896333862253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-979198999210525704653570310835800545000000000000)
      constant := (10478303386002710473284086699182165769650837716723) }

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
  base := (-1768231658943078314701189931464864658351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-104350747794891089874997837181505000000000000)
      constant := (1119656608000680881011358267358072859955299249) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel045
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
  base := (-1250595627199913573119329246813303186861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1001464048059281657868934545560027145000000000000)
      constant := (10973570059811914720037340880364551940135894467251) }

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
  base := (-125816537095110804252806500735861146917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-53361737215130820280082313921952500000000000)
      constant := (586286461708685339238055108724965986931261415) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel046
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
  base := (-180981761500049592522821165498223996673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-511864548454018805542149390142126872500000000000)
      constant := (5740051089837888292255666856551964530664288573886) }

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
  base := (-182727005417531925595668439133505993993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-54548100532816095622665709253152500000000000)
      constant := (613346333196810686561562432107320904216845614) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel047
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
  base := (-7224881901394205945068945815935790217/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1045994145756793564299663015008480345000000000000)
      constant := (11997886185414410079816087545744727976744641026175) }

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
  base := (-18705700651213832538895003089499715829/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-55734463850501370965249104584352500000000000)
      constant := (641007201291524375238336821236890555911472855) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel048
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
  base := (92475039969405900401705919043190427/2441406250000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-534129597302774758757513624866353472500000000000)
      constant := (6263454920818050395629735545109906285993745086464) }

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
  base := (372848799932078590793872464449137446283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-113841654336373292615664999831105000000000000)
      constant := (1338536838147760344160876732101382379008525483) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel049
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
  base := (119222962050057677799433909459995877047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (357542)
      previous := (178771)
      next := (178771)
      square := (4745957676913586606448625285400000000000000)
      linear := (-227097926583570485366595477812772500000000000)
      constant := (2721191609394045941548905757447310779828540892) }

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
  base := (474161655613564932562938640536832629227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (504406172485236115043960600000000000000)
      linear := (-24201245516814627926037440752500000000000)
      constant := (290766098707668632892140211100536832629227) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel050
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
  base := (1543954802884674614656792402682091333191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1112789292303061423945755719181160145000000000000)
      constant := (13618633023984679588929527098515540936946939879719) }

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
  base := (769464028998605471994524105614033452109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-59293553803557196992999290577952500000000000)
      constant := (727589626678735368352489235184579294318513709) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel051
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
  base := (2148893214850319559743486560647846294711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1135054341151817377161119953905386745000000000000)
      constant := (14181313600412783413477782018602517517724432853399) }

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
  base := (2144267523387276367916403658224618046443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-120959834242484944671165371818305000000000000)
      constant := (1515297230601529264683460039280877307929509643) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel052
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
  base := (2768239934604746260345238624984287968891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1157319390000573330376484188629613345000000000000)
      constant := (14755195727474414449639522902750400789363808301019) }

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
  base := (2763984935458337954665529533508808699993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-123332560877855495356332162480705000000000000)
      constant := (1576611881116974848457937964213314649688683193) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel053
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
  base := (425208879694538807964024051900152035139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-589792219424664641795924211676919972500000000000)
      constant := (7670136043693103770388039737618515508783773861004) }

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
  base := (339775847175566847083244393643452161627/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-62852643756613023020749476571552500000000000)
      constant := (819561216104046843970504642311509643200332135) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel054
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
  base := (4048894245693986719406176865629618484349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1201849487698085236807212658078066545000000000000)
      constant := (15936536077292985108837373959574339944346494618141) }

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
  base := (505662229459219872276703173992381865381/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-64039007074298298363332871902752500000000000)
      constant := (851414093436367978086023672724182835435119124) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel055
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
  base := (4709645835824448885930518017967942573479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1224114536546841190022576892802293145000000000000)
      constant := (16543981739421713214220919720900271583638947250311) }

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
  base := (2353170584098613458157049067439697207527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-65225370391983573705916267233952500000000000)
      constant := (883864258193702859811651854938622712995272327) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel056
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
  base := (269184392493111433680973115017254632117/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (17519558)
      previous := (8759779)
      next := (8759779)
      square := (232551926168765743715982638984600000000000000)
      linear := (-12718159034648950441203480893127752500000000000)
      constant := (175128609163868790000261868502866365928458537970) }

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
  base := (42036345798161511764250577412468461217/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (1862)
      previous := (931)
      next := (931)
      square := (24715902451776569637154069400000000000000)
      linear := (-1355341504278956103030605358472500000000000)
      constant := (18712478098150086324751587513325501094376512) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel057
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
  base := (6070805577663670360731824904740280191511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1268644634244353096453305362250746345000000000000)
      constant := (17792397102686482008548847535047575871218946724599) }

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
  base := (3034009024710374770203516756547992920863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-67598097027354124391083057896352500000000000)
      constant := (950555343495001591667344481066851731002992063) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel058
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
  base := (1692701321444583833939957532446071095079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-645454841546554524834334798487486472500000000000)
      constant := (9216678788334806260031976660880337116997139089422) }

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
  base := (6768246334124671406275641739960837454109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-137568920690078799467332906455105000000000000)
      constant := (1969591555039076168693700475526685970727315709) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel059
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
  base := (7483512168092784547176952785002212752143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1313174731941865002884033831699199545000000000000)
      constant := (19085481170962050997936993279103453939553577282287) }

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
  base := (7481163748102030345003162590382815477439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-139941647325449350152499697117505000000000000)
      constant := (2039265041508940660473707523351229139961331039) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel060
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
  base := (4104384248344402046859097381743616079767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-667719890395310478049699033211713072500000000000)
      constant := (9874382161165488760330282361728899879050561014903) }

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
  base := (2051653476622205320969159112733213705819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-71157186980409950418833243889952500000000000)
      constant := (1055065385459769091247563144787744892215342838) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel061
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
  base := (4473215976677985254786030621700460128739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-678852414819688454657381150573826372500000000000)
      constant := (10211601907832209773912354491500053246947483907651) }

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
  base := (8944455744047314112074318075295739502077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-144687100596190451522833278442305000000000000)
      constant := (2182188404573232944761873763863065070544486877) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel062
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
  base := (121204676551367268811166420870960031921/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-689984939244066431265063267935939672500000000000)
      constant := (10554398374980444212967705832462860213040703931560) }

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
  base := (9694562014455367737943138609418406772781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-147059827231561002208000069104705000000000000)
      constant := (2255437636951605486512890927895373594661447181) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel063
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
  base := (1045847914078761904622582901401649031227/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (17519558)
      previous := (8759779)
      next := (8759779)
      square := (232551926168765743715982638984600000000000000)
      linear := (-14308519666702947099443783373429652500000000000)
      constant := (222505515384099048436184726457114748980029636535) }

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
  base := (10456817936604491942480144166930641358447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3724)
      previous := (1862)
      next := (1862)
      square := (49431804903553139274308138800000000000000)
      linear := (-3049643956467990875370752240145000000000000)
      constant := (47548534540106414749639830395739601426563903) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel064
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
  base := (5616321227680901722933326442987834340713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-712249988092822384480427502660166272500000000000)
      constant := (11256716363430706578485984467326782192481556449417) }

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
  base := (2246223994701167391248797929240217498937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-151805280502302103578333650429505000000000000)
      constant := (2405509822521749225123827378761648811074738685) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel065
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
  base := (12018769733990396251042673671481964890681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1446765025034400722176219240044559145000000000000)
      constant := (23232471276523344456852565451063163880933058487129) }

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
  base := (12017374730813971998445652181973336696701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-154178007137672654263500441091905000000000000)
      constant := (2482332302881386814382643552107117981408779101) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel066
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
  base := (1602096982390133128121645222485671358403/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-734515036941578337695791737384392872500000000000)
      constant := (11981327116868054923168793674408551619864897594508) }

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
  base := (12815497963250808165544482606502460725193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-156550733773043204948667231754305000000000000)
      constant := (2560345431271214399051399110775892408201188393) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel067
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
  base := (6813292014541916371641843812762839467219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-745647561365956314303473854746506172500000000000)
      constant := (12351989931736245829719799334887933219394499633971) }

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
  base := (13625413678359864454938515872293004312929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-158923460408413755633834022416705000000000000)
      constant := (2639549025233343968242846736688935503355342529) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel068
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
  base := (14448124945650987707990131230062572658189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1513560171580668581822311944217238945000000000000)
      constant := (25456446600215603977140034877651687584484301622701) }

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
  base := (2889410665611295754752403089071707370937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-161296187043784306319000813079105000000000000)
      constant := (2719942920183824248272015796428145846988098685) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel069
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
  base := (3820334020242433695331481803505188323521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-767912610214712267518838089470732772500000000000)
      constant := (13110026515699080776903227627028875893801715645378) }

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
  base := (3056071015874708567503052702094487273527/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-163668913679154857004167603741505000000000000)
      constant := (2801526967661701212147822467519164319718691635) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel070
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
  base := (322523220322263357613932656749020723773/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (17519558)
      previous := (8759779)
      next := (8759779)
      square := (232551926168765743715982638984600000000000000)
      linear := (-15898880298756943757684085853731552500000000000)
      constant := (275457121249588560038620551017406962837725692325) }

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
  base := (8062631578322413155247304619000540858729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (1862)
      previous := (931)
      next := (931)
      square := (24715902451776569637154069400000000000000)
      linear := (-1694302452189034772340146881672500000000000)
      constant := (29431643201526533069737166166531026502077721) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel071
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
  base := (16982548844252718025095980840477310763639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1580355318126936441468404648389918745000000000000)
      constant := (27780680003363533603768077701871812743007165521751) }

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
  base := (16981727248127913548864542980012702795259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-168414366949895958374501185066305000000000000)
      constant := (2968264997649027794370426188166090499411416859) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel072
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
  base := (17850453632138794143611544329128002623411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1602620366975692394683768883114145345000000000000)
      constant := (28577698356431270802626944086381989059417501511699) }

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
  base := (557803186586071567114267549295823292043/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-85393546792633254529833987864352500000000000)
      constant := (1526709375197618184835022401486228347587123888) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel073
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
  base := (18729833934193115858321822875760720820801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1624885415824448347899133117838371945000000000000)
      constant := (29385852005365458538139265135782038204659202778209) }

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
  base := (18729146387312478530462751949642413321771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-173159820220637059744834766391105000000000000)
      constant := (3139762193697981209072142729432331434385572171) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel074
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
  base := (2452581544259095334274076736399331684657/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-823575232336602150557248676281299272500000000000)
      constant := (15102570052672488663157719362035976577478285795652) }

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
  base := (9810011785463955043466329632769532719253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-87766273428003805215000778526752500000000000)
      constant := (1613647619447918236671634262748239648058926453) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel075
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
  base := (20522875149068119218714521107462325688377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1669415513521960254329861587286825145000000000000)
      constant := (31035561894087970561888566727577514273037056002393) }

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
  base := (20522300212206369528907978923166320131707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-177905273491378161115168347715905000000000000)
      constant := (3316017806012946651576554101815522334636228507) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel076
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
  base := (10718235936574996522307543239131966609749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-845840281185358103772612911005525872500000000000)
      constant := (15938558341893959372009792510561320132368539146741) }

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
  base := (10717973132430853814354027425301379131887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-90139000063374355900167569189152500000000000)
      constant := (1702964911454089349738169101580388611295660687) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel077
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
  base := (5590353763722503198216576682252250545641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (17519558)
      previous := (8759779)
      next := (8759779)
      square := (232551926168765743715982638984600000000000000)
      linear := (-17489240930810940415924388334033452500000000000)
      constant := (333977590345280982576340303586520696562625744562) }

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
  base := (4472186925211583888605286740528094741147/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3724)
      previous := (1862)
      next := (1862)
      square := (49431804903553139274308138800000000000000)
      linear := (-3727565852288148213989835286545000000000000)
      constant := (71367984173624966717831470103069383211581015) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel078
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
  base := (23297679906847304739728166368608187573037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1736210660068228113975954291459504945000000000000)
      constant := (33593622844263523342012986715027339455436167024333) }

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
  base := (11648620424032490842441672760854054253189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-92511726698744906585334359851552500000000000)
      constant := (1794660976056140437378363584908130584261906789) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel079
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
  base := (1515327753959206060532935109298788501111/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-879237854458492033595659263091865772500000000000)
      constant := (17234286574901362173686886511292963898366560887992) }

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
  base := (12122421439080481817645466105582678924509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-93698090016430181927917755182752500000000000)
      constant := (1841400976386782930284501880084164012097746109) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel080
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
  base := (25204087343878833453966429908560820668671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1780740757765740020406682760907958145000000000000)
      constant := (35354654314557030158195836569937255776773332579039) }

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
  base := (25203720824013414606335189689203959980203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-189768906668230914541002301027905000000000000)
      constant := (3777471178729988112508890282306178707912467403) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel081
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
  base := (26174191539606772097014078323819913215151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1803005806614495973622046995632184745000000000000)
      constant := (36251865927170482199803655427176294962572695177359) }

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
  base := (26173856742044084064802624647106860573023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-192141633303601465226169091690305000000000000)
      constant := (3873329586899016251046141138795583572235828223) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel082
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
  base := (6788885055185439427838923487748949032677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-912635427731625963418705615178205672500000000000)
      constant := (18580103808238780640539504265304008308425494802186) }

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
  base := (6788808611631382889186872890812308570477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-97257179969486007955667941176352500000000000)
      constant := (1985188569209359345825416297319560705755430554) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel083
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
  base := (7037029640682372401173658880448075254623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-923767952156003940026387732540318972500000000000)
      constant := (19039839523788313887046758113335285292344730969214) }

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
  base := (2814783933737873353805061298910384733493/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-98443543287171283298251336507552500000000000)
      constant := (2034306899117152849396767252391439168725583465) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel084
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
  base := (29151913189420877501927461401318286409603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (35039116)
      previous := (17519558)
      next := (17519558)
      square := (465103852337531487431965277969200000000000000)
      linear := (-38159203125729874148329381628670705000000000000)
      constant := (796128161597693412144908248764472579084569776723) }

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
  base := (1821978640302483707828279808070206812839/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (1862)
      previous := (931)
      next := (931)
      square := (24715902451776569637154069400000000000000)
      linear := (-2033263400099113441649688404872500000000000)
      constant := (42531015660460959457992454907403521070632888) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel085
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
  base := (30166912031564104905846289457381063981753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1892066002009519786483503934529091145000000000000)
      constant := (39952009955952033134345200678854469776591357858777) }

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
  base := (30166679289342885015878451841799230703249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-201632539845083667966836254339905000000000000)
      constant := (4268654319368486516890169232735959952918500849) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel086
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
  base := (31193104199121695643280531741792224563943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1914331050858275739698868169253317745000000000000)
      constant := (40904868914554860957262223383983694903754057388487) }

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
  base := (31192891755129951452667573803278979192731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-204005266480454218652003045002305000000000000)
      constant := (4370458126435707684617676885832952829041747131) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel087
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
  base := (32230479866061921732776305830185344527139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-1936596099707031692914232403977544345000000000000)
      constant := (41868856572115489462736995813913028061130697893251) }

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
  base := (3223028597624067217771751801556657602259/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-103188996557912384668584917832352500000000000)
      constant := (2236725466359433465150180029188267674515119295) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel088
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
  base := (4159878770800730721808693967551736533393/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-979430574277893823064798319350885472500000000000)
      constant := (21421986364171254341079376195404628556966040254148) }

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
  base := (33278853233671713207168311620807172711103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-208750719751195320022336626327105000000000000)
      constant := (4577632717283637249042970955534998021679358303) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel089
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
  base := (17169373550215177307695490361350411921689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-990563098702271799672480436712998772500000000000)
      constant := (21915108601257050884390372767901285057251583494201) }

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
  base := (6867717132522011911226377140631406784433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-211123446386565870707503416989505000000000000)
      constant := (4683003461246602591866793323841400038447118165) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel090
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
  base := (35409623450034972531376992438779700309357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-2003391246253299552560325108150224145000000000000)
      constant := (44827589831566095912614113836178786896205986771213) }

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
  base := (35409476168753917699203152462076559999873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-213496173021936421392670207651905000000000000)
      constant := (4789563147574344352517329547486645820559695073) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel091
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
  base := (291933221619017423961085341834440856201/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (35039116)
      previous := (17519558)
      next := (17519558)
      square := (465103852337531487431965277969200000000000000)
      linear := (-41339924389837867464809986589274505000000000000)
      constant := (935430417721771573352104322460854342097970655125) }

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
  base := (1140359948525966209136138644977594639469/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (1862)
      previous := (931)
      next := (931)
      square := (24715902451776569637154069400000000000000)
      linear := (-2202743874054152776304459166472500000000000)
      constant := (49972568988798056868979326328322434197343696) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel092
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
  base := (9396207245242103413066331172820416316109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-1023960671975405729495526788799338672500000000000)
      constant := (23427859490080214713053717421763045993261930527962) }

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
  base := (18792353221255305975196196928399302086643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-109120813146338761381501894488352500000000000)
      constant := (2503124643685416420969831498028366724310029843) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel093
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
  base := (19344573491750949805591381598721473566889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-1035093196399783706103208906161451972500000000000)
      constant := (23943237623581251361442653933343798774717851501001) }

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
  base := (38689035230986902368623900630009763657773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-220614352928048073448170579639105000000000000)
      constant := (5116375714478672724510042811643493442542312973) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel094
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
  base := (39804601925754570388268663538527910165601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1716916684)
      previous := (858458342)
      next := (858458342)
      square := (22790088764539042884166298620490800000000000000)
      linear := (-2092451441648323365421782047047130545000000000000)
      constant := (48928359161292600654238697465940585857802283681409) }

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
  base := (9951125005394260105104932684544875608989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-111493539781709312066668685150752500000000000)
      constant := (2613845515474496969628835926389944492674365178) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel095
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
  base := (20465594745484854548569918769639142517149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-1057358245248539659318573140885678572500000000000)
      constant := (24990685312515416689088434529884551885982195713341) }

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
  base := (2046554828887389045091363636720735519399/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-112679903099394587409252080481952500000000000)
      constant := (2670097613304940082223929949690964859820769990) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel096
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
  base := (2629306611511551775093772485148932976709/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (858458342)
      previous := (429229171)
      next := (429229171)
      square := (11395044382269521442083149310245400000000000000)
      linear := (-1068490769672917635926255258247791872500000000000)
      constant := (25522754775193034144311587684977763149737838475048) }

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
  base := (42068821078037062035077822884912604370577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-227732532834159725503670951626305000000000000)
      constant := (5453888292286000989752184293784755163093755377) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel097
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
  base := (43217747291021659634251676664055603647093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2422158440274103824441098801200000000000000)
      linear := (-229487361908235861947908890553705000000000000)
      constant := (5539459651181310903253775637103326254356670293) }

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
  base := (10804417518847909222027906964216846915423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1211079220137051912220549400600000000000000)
      linear := (-115052629734765138094418871144352500000000000)
      constant := (2784385109850490784643384784118149298887861246) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell064.Kernel098
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
  base := (44377710840502312677320595464039582548287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (715084)
      previous := (357542)
      next := (357542)
      square := (9491915353827173212897250570800000000000000)
      linear := (-908584605182568587373277378568945000000000000)
      constant := (22160420439871679018739385796609995932196832383) }

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
  base := (22188820230244033777226573517843481157709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (504406172485236115043960600000000000000)
      linear := (-48412741796105961448147549552500000000000)
      constant := (1183848605037346174227023729637843481157709) }

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
end ForestUnimodality.Stage80KernelData.Cell064.Kernel098
