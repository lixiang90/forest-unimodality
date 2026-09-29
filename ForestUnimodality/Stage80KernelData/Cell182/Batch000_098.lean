import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell182.Parameters
import ForestUnimodality.BinomialMassData.Q2557_4752.Batch000_049
import ForestUnimodality.BinomialMassData.Q2557_4752.Batch050_099
import ForestUnimodality.BinomialMassData.Q427_792.Batch000_049
import ForestUnimodality.BinomialMassData.Q427_792.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree000.table
  base := (21672104511349690279109481/625000000000000000000000)
  polynomial :=
    { denominator := 4320000000000000000000000000000000000000000
      center := (17899)
      previous := (0)
      next := (15365)
      square := (823833461126848081157447716800000000000000)
      linear := (-3028623356424093877592440560000000000000000)
      constant := (149797586382449059209204732672000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree000.table
  base := (21672104511349690279109481/625000000000000000000000)
  polynomial :=
    { denominator := 720000000000000000000000000000000000000000
      center := (2989)
      previous := (0)
      next := (2555)
      square := (137305576854474680192907952800000000000000)
      linear := (-504770559404015646265406760000000000000000)
      constant := (24966264397074843201534122112000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree001.table
  base := (218171511312480919906434492938551622912273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-12791007975576871695433944800824200000000000000)
      constant := (314018470535660845204756453900241582937499024912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree001.table
  base := (108961987444601164350946372624368404048729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-710926212812339931999550125215400000000000000)
      constant := (17426809612320539975805077608785718149305486864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (6230819941265383747/12500000000000000000)
  directionHi := (49846559530123069977/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree002.table
  base := (140300874246698103038629004046037152706923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-15687503445716228692773386292128400000000000000)
      constant := (211778204214999421594388774725957784249999534512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree002.table
  base := (70001991784968815573843952455360531964567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-872157286433706825216072288790800000000000000)
      constant := (11744011871203359558189044317600867180555538672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6230819941265383747/12500000000000000000)
  centralHi := (49846559530123069977/100000000000000000000)
  directionLo := (1409873610502757953/2000000000000000000)
  directionHi := (70493680525137897651/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree003.table
  base := (46091243403627780311268270330082633182041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-2064888768428398410012536420381400000000000000)
      constant := (17009685543936174754286487073908857660149882912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree003.table
  base := (91911224332155647566599683873599877038381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-114820928895008190936954939151800000000000000)
      constant := (942981565796315331004903055919564628758375272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1409873610502757953/2000000000000000000)
  centralHi := (70493680525137897651/100000000000000000000)
  directionLo := (86336773688679780039/100000000000000000000)
  directionHi := (2158419342216994501/2500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree004.table
  base := (61699259858586615153959901690217295648379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-21480494385994942687452269274736800000000000000)
      constant := (120843986527992081891841586141728138909565811376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree004.table
  base := (30737391924956070878894126608524080752567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-1194619433676440611649116615941600000000000000)
      constant := (6700979303150339566334877859826512247294546672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86336773688679780039/100000000000000000000)
  centralHi := (2158419342216994501/2500000000000000000)
  directionLo := (6230819941265383747/6250000000000000000)
  directionHi := (99693119060246139953/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree005.table
  base := (41809324199091214273118200614038502990421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-24376989856134299684791710766041000000000000000)
      constant := (105110154266235924606515786647879088214512735824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree005.table
  base := (2601959752283874515658045837187279391169/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-1355850507297807504865638779517000000000000000)
      constant := (5832627800510625475784699031803945740044463232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6230819941265383747/6250000000000000000)
  centralHi := (99693119060246139953/100000000000000000000)
  directionLo := (111460295553845160497/100000000000000000000)
  directionHi := (55730147776922580249/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree006.table
  base := (14196042444838556806210613533336766233213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-3030387258474850742459016917482800000000000000)
      constant := (11118899574048766266429860814035001667255059616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree006.table
  base := (3531666979725794411219143983890769931971/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-168564620102130488675795660343600000000000000)
      constant := (617571369683881827360691269842301101178650816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111460295553845160497/100000000000000000000)
  centralHi := (55730147776922580249/50000000000000000000)
  directionLo := (122098636282067533599/100000000000000000000)
  directionHi := (152623295352584417/125000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree007.table
  base := (19014129800952974839231911806569960248011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-30169980796413013679470593748649400000000000000)
      constant := (102289430620257308258163136325386355226268836784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree007.table
  base := (18906254149158315031608199589460117362683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-1678312654540541291298683106667800000000000000)
      constant := (5686641029533957900234594793695751382173248664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122098636282067533599/100000000000000000000)
  centralHi := (152623295352584417/125000000000000000)
  directionLo := (26376320045776455019/20000000000000000000)
  directionHi := (16485200028610284387/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree008.table
  base := (12221599227216582669726301930614142352719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-33066476266552370676810035239953600000000000000)
      constant := (109716261455206572859865720659001086124655844336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree008.table
  base := (12137312219173909917324275286771773912309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-1839543728161908184515205270243200000000000000)
      constant := (6104212863146039859849812231302001248916324072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26376320045776455019/20000000000000000000)
  centralHi := (16485200028610284387/12500000000000000000)
  directionLo := (1409873610502757953/1000000000000000000)
  directionHi := (140987361050275795301/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree009.table
  base := (3566573305521553617204934733742671693919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2165779)
      previous := (0)
      next := (1859165)
      square := (99683848796348617820051173732800000000000000)
      linear := (-1331961916173767691635165804861400000000000000)
      constant := (4485433536872018559838689453407537619569067936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree009.table
  base := (1766679061379677979929953769350065163513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-222308311309252786414636381535400000000000000)
      constant := (749097217281971610259624631139173570818101024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1409873610502757953/1000000000000000000)
  centralHi := (140987361050275795301/100000000000000000000)
  directionLo := (149539678590369209929/100000000000000000000)
  directionHi := (14953967859036920993/10000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree010.table
  base := (3204967503270080272986711003867624959189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-38859467206831084671488918222562000000000000000)
      constant := (135693267594772338421140758567430674280401640016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree010.table
  base := (788023479607291397398822805735846504899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-2162005875404641970948249597394000000000000000)
      constant := (7557100978645130942034186569634795011024483168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149539678590369209929/100000000000000000000)
  centralHi := (14953967859036920993/10000000000000000000)
  directionLo := (157628661638361411633/100000000000000000000)
  directionHi := (78814330819180705817/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree011.table
  base := (94505617168047145123365778265390828871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 116640000000000000000000000000000000000000000
      center := (483273)
      previous := (0)
      next := (414855)
      square := (22243503450424898191251088353600000000000000)
      linear := (-345090600636119352634945121602200000000000000)
      constant := (1264400685892166854102870766862068768627951344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree011.table
  base := (52027557380615720576980144480183940267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6480000000000000000000000000000000000000000
      center := (26901)
      previous := (0)
      next := (22995)
      square := (1235750191690272121736171575200000000000000)
      linear := (-19200305363851312926981584801400000000000000)
      constant := (70439016983253074739844264306385659193293016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157628661638361411633/100000000000000000000)
  centralHi := (78814330819180705817/50000000000000000000)
  directionLo := (16532233505153238537/10000000000000000000)
  directionHi := (165322335051532385371/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree012.table
  base := (-1209554749891899080989883928220610656069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-4961384238567755407351977911685600000000000000)
      constant := (19188069722460169938915087435954413438715767392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree012.table
  base := (-490701676471836685346819082843473172849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-276052002516375084153477102727200000000000000)
      constant := (1069187046845761319206970545095538308590697560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16532233505153238537/10000000000000000000)
  centralHi := (165322335051532385371/100000000000000000000)
  directionLo := (86336773688679780039/50000000000000000000)
  directionHi := (172673547377359560079/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree013.table
  base := (-179275883148374469191608607135106433531/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-47548953617249155663507242696474600000000000000)
      constant := (194587617756609020627863327971138189891865608400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree013.table
  base := (-1127481803430032717464369187292909159279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-2645699096268742650597816088120200000000000000)
      constant := (10844386511519612907893251150057812814557008672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86336773688679780039/50000000000000000000)
  centralHi := (172673547377359560079/100000000000000000000)
  directionLo := (179724326291326905781/100000000000000000000)
  directionHi := (89862163145663452891/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree014.table
  base := (-3096446421281521291881843065930431047383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-50445449087388512660846684187778800000000000000)
      constant := (218537680282977309541147222437303688447724574496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree014.table
  base := (-1243167220005957880710633375994189240581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-2806930169890109543814338251695600000000000000)
      constant := (12180498734234717605001162396906688050122624760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179724326291326905781/100000000000000000000)
  centralHi := (89862163145663452891/50000000000000000000)
  directionLo := (37301749534230397923/20000000000000000000)
  directionHi := (11656796729446999351/6250000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree015.table
  base := (-1524191502758652293564316564287213275709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-5926882728614207739798458408787000000000000000)
      constant := (27160625434864794695964273665583213064782087280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree015.table
  base := (-238743516802424135683975526925705392371/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-329795693723497381892317823919000000000000000)
      constant := (1513960514842251649450797523920606647893243136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37301749534230397923/20000000000000000000)
  centralHi := (11656796729446999351/6250000000000000000)
  directionLo := (193054894925903253463/100000000000000000000)
  directionHi := (24131861865737906683/12500000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree016.table
  base := (-1763017019959491963758787535416778646567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-56238440027667226655525567170387200000000000000)
      constant := (272242316250650214208235604340115309789197719760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree016.table
  base := (-8830573596333297594521384351163753018049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-3129392317132843330247382578846400000000000000)
      constant := (15175999697077583545400538010821152453360814008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193054894925903253463/100000000000000000000)
  centralHi := (24131861865737906683/12500000000000000000)
  directionLo := (39877247624098455981/20000000000000000000)
  directionHi := (99693119060246139953/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree017.table
  base := (-4905425420215473871042714792896744767533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-59134935497806583652865008661691400000000000000)
      constant := (301877533392260142589416385367824054555621811296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree017.table
  base := (-9823596353429927395256395432447761814403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-3290623390754210223463904742421800000000000000)
      constant := (16828786942519310003203395952730998391656289576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39877247624098455981/20000000000000000000)
  centralHi := (99693119060246139953/50000000000000000000)
  directionLo := (3211291094005250627/1562500000000000000)
  directionHi := (205522630016336040129/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree018.table
  base := (-531726818716205929762995946322405450501/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2165779)
      previous := (0)
      next := (1859165)
      square := (99683848796348617820051173732800000000000000)
      linear := (-2297460406220220024081646301962800000000000000)
      constant := (12344969922430435686088266559659279445828234560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree018.table
  base := (-10645024385788415785346450048580478274001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-383539384930619679631158545110800000000000000)
      constant := (2064661659574896317111010247986216873276903288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3211291094005250627/1562500000000000000)
  centralHi := (205522630016336040129/100000000000000000000)
  directionLo := (4229620831508273859/2000000000000000000)
  directionHi := (211481041575413692951/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree019.table
  base := (-2826458635161888643129670608972601880937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-64927926438085297647543891644299800000000000000)
      constant := (366524486420328710856843232854162319933803402688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree019.table
  base := (-1131446017013301618436667623890306412937/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-3613085537996944009896949069572600000000000000)
      constant := (20433966687046858835665580208947351047744357040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4229620831508273859/2000000000000000000)
  centralHi := (211481041575413692951/100000000000000000000)
  directionLo := (217276115674990742787/100000000000000000000)
  directionHi := (54319028918747685697/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree020.table
  base := (-11839668748191128800800945580852013954083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-67824421908224654644883333135604000000000000000)
      constant := (401487366872925849888329578370790495217988682448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree020.table
  base := (-11846756299845708939491376805500225495553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-3774316611618310903113471233148000000000000000)
      constant := (22383657632995791633141617149839338319344680376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217276115674990742787/100000000000000000000)
  centralHi := (54319028918747685697/25000000000000000000)
  directionLo := (44584118221538064199/20000000000000000000)
  directionHi := (55730147776922580249/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree021.table
  base := (-12247448034912510838800868933265571878111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-7857879708707112404691419402989800000000000000)
      constant := (48687414131793983492577398033605707330362145424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree021.table
  base := (-2450653036525131113389399983885132929717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-437283076137741977369999266302600000000000000)
      constant := (2714459739381998821140324411817326109581527480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44584118221538064199/20000000000000000000)
  centralHi := (55730147776922580249/25000000000000000000)
  directionLo := (57106408044977844273/25000000000000000000)
  directionHi := (228425632179911377093/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree022.table
  base := (-6268976813643660204444379075576070420731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 116640000000000000000000000000000000000000000
      center := (483273)
      previous := (0)
      next := (414855)
      square := (22243503450424898191251088353600000000000000)
      linear := (-608408370648788170574894348084400000000000000)
      constant := (3938927058088344697933845024632486429225187232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree022.table
  base := (-391960063561593090197579327981032256383/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6480000000000000000000000000000000000000000
      center := (26901)
      previous := (0)
      next := (22995)
      square := (1235750191690272121736171575200000000000000)
      linear := (-33857675693066485037574508762800000000000000)
      constant := (219609271409889878454472348116035315131642112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57106408044977844273/25000000000000000000)
  centralHi := (228425632179911377093/100000000000000000000)
  directionLo := (233801088393066012937/100000000000000000000)
  directionHi := (116900544196533006469/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree023.table
  base := (-6358989329034678286121903965617606387337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-76513908318642725636901657609516600000000000000)
      constant := (516748119953404143156524686044976451111740498144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree023.table
  base := (-3180470542980605447169314297867394704049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-4258009832482411582763037723874200000000000000)
      constant := (28810880520494910772724145573582615764179704032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233801088393066012937/100000000000000000000)
  centralHi := (116900544196533006469/50000000000000000000)
  directionLo := (59763925380812070077/25000000000000000000)
  directionHi := (239055701523248280309/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree024.table
  base := (-1279279828774264409695673207596996947729/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-8823378198753564737137899900091200000000000000)
      constant := (62065902210465665566720964012775093266449291360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree024.table
  base := (-6397994720375810424989464937289999763807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-491026767344864275108839987494400000000000000)
      constant := (3460466948310116149868156983069459044115426832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59763925380812070077/25000000000000000000)
  centralHi := (239055701523248280309/100000000000000000000)
  directionLo := (122098636282067533599/50000000000000000000)
  directionHi := (244197272564135067199/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree025.table
  base := (-6383260233817267005765256946896741505167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-82306899258921439631580540592125000000000000000)
      constant := (602139376118592100371915703716066211764263171104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree025.table
  base := (-6384562869916827430540768903948914482089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-4580471979725145369196082051025000000000000000)
      constant := (33572367829918877843425676981284909526576731376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122098636282067533599/50000000000000000000)
  centralHi := (244197272564135067199/100000000000000000000)
  directionLo := (249232797650615349881/100000000000000000000)
  directionHi := (124616398825307674941/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree026.table
  base := (-12642350857186131137147855967976857283673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-85203394729060796628919982083429200000000000000)
      constant := (647382364338389227328058488653563395333831813488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree026.table
  base := (-790279688026457668321072924830885631987/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-4741703053346512262412604214600400000000000000)
      constant := (36095126759569317986671645230695208709874612864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249232797650615349881/100000000000000000000)
  centralHi := (124616398825307674941/50000000000000000000)
  directionLo := (254168579729561929419/100000000000000000000)
  directionHi := (12708428986478096471/5000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree027.table
  base := (-12422794827483694461622266408245799721719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2165779)
      previous := (0)
      next := (1859165)
      square := (99683848796348617820051173732800000000000000)
      linear := (-3262958896266672356528126799064200000000000000)
      constant := (25715501800486370587556309745846469306946304432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree027.table
  base := (-2484904899837949680434595661003356171449/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-544770458551986572847680708686200000000000000)
      constant := (4301364922581676122174037768880456305171681560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254168579729561929419/100000000000000000000)
  centralHi := (12708428986478096471/5000000000000000000)
  directionLo := (259010321066039340117/100000000000000000000)
  directionHi := (129505160533019670059/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree028.table
  base := (-6054906314789080140362335120432706049507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-90996385669339510623598865066037600000000000000)
      constant := (742945162354261203344382806758670945826529185184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree028.table
  base := (-3027804839528335316764245247182693605521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-5064165200589246048845648541751200000000000000)
      constant := (41423687945910147251372278226141397439113237728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259010321066039340117/100000000000000000000)
  centralHi := (129505160533019670059/50000000000000000000)
  directionLo := (263763200457764550191/100000000000000000000)
  directionHi := (16485200028610284387/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree029.table
  base := (-5852469626614029827535200619126679573487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-93892881139478867620938306557341800000000000000)
      constant := (793260039163191055507932731888313182338073126944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree029.table
  base := (-5853040999277563381744643333716818848807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-5225396274210612942062170705326600000000000000)
      constant := (44229218318207693156590765781843125835405481488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263763200457764550191/100000000000000000000)
  centralHi := (16485200028610284387/6250000000000000000)
  directionLo := (16776996133647111001/6250000000000000000)
  directionHi := (268431938138353776017/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree030.table
  base := (-11209377398926553113967430689299854386899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-10754375178846469402030860894294000000000000000)
      constant := (93917942401755193688954945455114879034464046416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree030.table
  base := (-11210304668271825021277846843195373973447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-598514149759108870586521429878000000000000000)
      constant := (5236531326485068211475980080628331901943329736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16776996133647111001/6250000000000000000)
  centralHi := (268431938138353776017/100000000000000000000)
  directionLo := (273020850686725191591/100000000000000000000)
  directionHi := (34127606335840648949/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree031.table
  base := (-2656017454725482263669171990669097793673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-99685872079757581615617189539950200000000000000)
      constant := (898948159164377384962624309282934832623945493952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree031.table
  base := (-2656205362271042860121065416168981272691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-5547858421453346728495215032477400000000000000)
      constant := (50122305566896509270203413113120852565483376288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273020850686725191591/100000000000000000000)
  centralHi := (34127606335840648949/12500000000000000000)
  directionLo := (6938347444037610791/2500000000000000000)
  directionHi := (277533897761504431641/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree032.table
  base := (-4974877867283510289777798436032004782861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-102582367549896938612956631031254400000000000000)
      constant := (954319028513227307272008596494120092483475649632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree032.table
  base := (-1990072877095078950700326091492923071689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-5709089495074713621711737196052800000000000000)
      constant := (53209731805656538258900064812319914438975044440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6938347444037610791/2500000000000000000)
  centralHi := (277533897761504431641/100000000000000000000)
  directionLo := (1409873610502757953/500000000000000000)
  directionHi := (281974722100551590601/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree033.table
  base := (-9187014909765321101847101487005711426967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12960000000000000000000000000000000000000000
      center := (53697)
      previous := (0)
      next := (46095)
      square := (2471500383380544243472343150400000000000000)
      linear := (-96858460073495220946093730507400000000000000)
      constant := (928717420951445894178996713567221847990650768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree033.table
  base := (-1148438414141270708108551133146256838657/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 720000000000000000000000000000000000000000
      center := (2989)
      previous := (0)
      next := (2555)
      square := (137305576854474680192907952800000000000000)
      linear := (-5390560669142406349796381413800000000000000)
      constant := (51782383527398840412095798510070256060933568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1409873610502757953/500000000000000000)
  centralHi := (281974722100551590601/100000000000000000000)
  directionLo := (286346683935179177191/100000000000000000000)
  directionHi := (35793335491897397149/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree034.table
  base := (-208407553082837483157632598574036057807/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-108375358490175652607635514013862800000000000000)
      constant := (1070110246023714966952938309500419751161217495680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree034.table
  base := (-4168350062172460136051878934895009937037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-6031551642317447408144781523203600000000000000)
      constant := (59666121858783727158285910081328954121713605808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286346683935179177191/100000000000000000000)
  centralHi := (35793335491897397149/12500000000000000000)
  directionLo := (145326445371845092587/50000000000000000000)
  directionHi := (11626115629747607407/4000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree035.table
  base := (-1479594831313702854577292594981576919817/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-111271853960315009604974955505167000000000000000)
      constant := (1130529448794771015876980115743208637768388979760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree035.table
  base := (-1849573895156498402790656826756753116331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-6192782715938814301361303686779000000000000000)
      constant := (63035022738671519389941665570144688506618875808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145326445371845092587/50000000000000000000)
  centralHi := (11626115629747607407/4000000000000000000)
  directionLo := (58979244618646518157/20000000000000000000)
  directionHi := (147448111546616295393/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree036.table
  base := (-637231093513963896039574208373137079233/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2165779)
      previous := (0)
      next := (1859165)
      square := (99683848796348617820051173732800000000000000)
      linear := (-4228457386313124688974607296165600000000000000)
      constant := (44171499431776430804207417967669493785943326240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree036.table
  base := (-6372570307001138022175647329086845743027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-706001532173353466064202872261600000000000000)
      constant := (7388632956820615322028292067846795399886748776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58979244618646518157/20000000000000000000)
  centralHi := (147448111546616295393/50000000000000000000)
  directionLo := (149539678590369209929/50000000000000000000)
  directionHi := (299079357180738419859/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree037.table
  base := (-5259532098978728249207033151449426099873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-117064844900593723599653838487775400000000000000)
      constant := (1256413043625764603816739287587688692420500840688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree037.table
  base := (-164366913697163708451703586644147272581/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-6515244863181548087794348013929800000000000000)
      constant := (70054126467498935375183039677190844920847006464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149539678590369209929/50000000000000000000)
  centralHi := (299079357180738419859/100000000000000000000)
  directionLo := (303204784574112241821/100000000000000000000)
  directionHi := (151602392287056120911/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree038.table
  base := (-4059809993936046945134836649852406031339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-119961340370733080596993279979079600000000000000)
      constant := (1321876882458892236054299662771187230862105890384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree038.table
  base := (-811995701420334634976107637804354514619/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-6676475936802914981010870177505200000000000000)
      constant := (73704298967258623404385653128954230856088767240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303204784574112241821/100000000000000000000)
  centralHi := (151602392287056120911/50000000000000000000)
  directionLo := (38409353695914666957/12500000000000000000)
  directionHi := (307274829567317335657/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree039.table
  base := (-1386639930099784048093941238872128927619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-13650870648985826399370302385598200000000000000)
      constant := (154335756698546519310312508643030487710172997792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree039.table
  base := (-2773415545562992009277034822889226717019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-759745223380475763803043593453400000000000000)
      constant := (8605355960945986194701214478599851556841330472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38409353695914666957/12500000000000000000)
  centralHi := (307274829567317335657/100000000000000000000)
  directionLo := (15564583224633258629/5000000000000000000)
  directionHi := (311291664492665172581/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree040.table
  base := (-8750298899403270738474285585051039303/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-125754331311011794591672162961688000000000000000)
      constant := (1457847677329359714702722913026450276157751482880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree040.table
  base := (-1400157005119987090394654234385622798659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-6998938084045648767443914504656000000000000000)
      constant := (81285832305755620518350286281810292087602745128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15564583224633258629/5000000000000000000)
  centralHi := (311291664492665172581/100000000000000000000)
  directionLo := (157628661638361411633/50000000000000000000)
  directionHi := (315257323276722823267/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree041.table
  base := (14950708391672319053688663989766469739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-128650826781151151589011604452992200000000000000)
      constant := (1528354366047535999501994714672694773123869276864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree041.table
  base := (29857517003794310776521573708212815047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-7160169157667015660660436668231400000000000000)
      constant := (85217178503237987312399296206066389600804410352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157628661638361411633/50000000000000000000)
  centralHi := (315257323276722823267/100000000000000000000)
  directionLo := (319173713479970378777/100000000000000000000)
  directionHi := (159586856739985189389/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree042.table
  base := (80310337846618511694497308122285250267/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-14616369139032278731816782882699600000000000000)
      constant := (177837976022518092595309448289978810676117397440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree042.table
  base := (803068096802899110357682314892215564431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-813488914587598061541884314645200000000000000)
      constant := (9915804132577108641060446551946131963994645744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319173713479970378777/100000000000000000000)
  centralHi := (159586856739985189389/50000000000000000000)
  directionLo := (323042627022478765827/100000000000000000000)
  directionHi := (80760656755619691457/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree043.table
  base := (1619556328876454462300331276432613226209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-134443817721429865583690487435600600000000000000)
      constant := (1674409859409108702444727464221571951412261429792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree043.table
  base := (3239055979034161022921029421256140914877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-7482631304909749447093480995382200000000000000)
      constant := (93361004416439821080299952781859713996853675816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323042627022478765827/100000000000000000000)
  centralHi := (80760656755619691457/25000000000000000000)
  directionLo := (326865749766742051019/100000000000000000000)
  directionHi := (16343287488337102551/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree044.table
  base := (1239620071558716552512064689535254472891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 116640000000000000000000000000000000000000000
      center := (483273)
      previous := (0)
      next := (414855)
      square := (22243503450424898191251088353600000000000000)
      linear := (-1135043910674125806454792801048800000000000000)
      constant := (14462467230252637480955529261005056832687202496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree044.table
  base := (4958434784657917927877563458540621372021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6480000000000000000000000000000000000000000
      center := (26901)
      previous := (0)
      next := (22995)
      square := (1235750191690272121736171575200000000000000)
      linear := (-63172416351496829258760356685600000000000000)
      constant := (806392372459313281430837730105334322649069608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326865749766742051019/100000000000000000000)
  centralHi := (16343287488337102551/5000000000000000000)
  directionLo := (330644670103064770741/100000000000000000000)
  directionHi := (165322335051532385371/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree045.table
  base := (1352855611009160692367916951487038157187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2165779)
      previous := (0)
      next := (1859165)
      square := (99683848796348617820051173732800000000000000)
      linear := (-5193955876359577021421087793267000000000000000)
      constant := (67673620962090815494329957843219246042762394320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree045.table
  base := (3382120772651441671509545476955930224843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-867232605794720359280725035837000000000000000)
      constant := (11319961412316339793788483495712042628237664432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330644670103064770741/100000000000000000000)
  centralHi := (165322335051532385371/50000000000000000000)
  directionLo := (334380886661535481493/100000000000000000000)
  directionHi := (167190443330767740747/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree046.table
  base := (4328240587351300168422132853840725339481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-143133304131847936575708811909513200000000000000)
      constant := (1906097517770269086901041932024982694327048944928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree046.table
  base := (8656451894316936910483335141952737618863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-7966324525773850126743047486108400000000000000)
      constant := (106279529435709814900175645741225680251219810104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334380886661535481493/100000000000000000000)
  centralHi := (167190443330767740747/50000000000000000000)
  directionLo := (338075815256792274931/100000000000000000000)
  directionHi := (84518953814198068733/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree047.table
  base := (2127014038073321896336100910561184287757/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-146029799601987293573048253400817400000000000000)
      constant := (1986687762784550544947706972371493501637100577040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree047.table
  base := (2658761679732470153990312214396224379021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-8127555599395217019959569649683800000000000000)
      constant := (110773105743571091635463304412077879144441114272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338075815256792274931/100000000000000000000)
  centralHi := (84518953814198068733/25000000000000000000)
  directionLo := (341730795156852733097/100000000000000000000)
  directionHi := (170865397578426366549/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree048.table
  base := (12700029833615588207627175176761611380897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-16547366119125183396709743876902400000000000000)
      constant := (229884275496700030089070394865480648850306743952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree048.table
  base := (6350005513600088686874406114589010967103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-920976297001842657019565757028800000000000000)
      constant := (12817820050993637367793716298207798927090802672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341730795156852733097/100000000000000000000)
  centralHi := (170865397578426366549/50000000000000000000)
  directionLo := (86336773688679780039/25000000000000000000)
  directionHi := (345347094754719120157/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree049.table
  base := (371283703034483079163863169469863862217/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-151822790542266007567727136383425800000000000000)
      constant := (2152909650915284017275218841264340402960271585920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree049.table
  base := (1485133305933485420942999956405102185909/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-8450017746637950806392613976834600000000000000)
      constant := (120041352659762901499238060814090875021927528720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86336773688679780039/25000000000000000000)
  centralHi := (345347094754719120157/100000000000000000000)
  directionLo := (174462958355430744917/50000000000000000000)
  directionHi := (69785183342172297967/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree050.table
  base := (213612695610371634544428114322894078899/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-154719286012405364565066577874730000000000000000)
      constant := (2238541263846054097555290560627177574671170420480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree050.table
  base := (17089003590671639127357185081316073343907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-8611248820259317699609136140410000000000000000)
      constant := (124816021622744267780112407760512080678749060056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174462958355430744917/50000000000000000000)
  centralHi := (69785183342172297967/20000000000000000000)
  directionLo := (1409873610502757953/400000000000000000)
  directionHi := (352468402625689488251/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree051.table
  base := (9706512517236674147338413228433972195557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-17512864609171635729156224374003800000000000000)
      constant := (258428145316087111335045087380106384817636933024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree051.table
  base := (2426626923123031868676174569736498999773/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-974719988208964954758406478220600000000000000)
      constant := (14409376308945422801309375370340717534288179008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1409873610502757953/400000000000000000)
  centralHi := (352468402625689488251/100000000000000000000)
  directionLo := (355975637293474419009/100000000000000000000)
  directionHi := (35597563729347441901/10000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree052.table
  base := (21823370484683305431311473371648146498913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-160512276952684078559745460857338400000000000000)
      constant := (2414845774734673208978501658420422281672361869072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree052.table
  base := (4364672553137869430058191432297165393519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-8933710967502051486042180467560800000000000000)
      constant := (134646447687966966132634589102687580720875188760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (355975637293474419009/100000000000000000000)
  centralHi := (35597563729347441901/10000000000000000000)
  directionLo := (179724326291326905781/50000000000000000000)
  directionHi := (359448652582653811563/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree053.table
  base := (304000593149514034310845338785820578729/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-163408772422823435557084902348642600000000000000)
      constant := (2505518658097637024493913457379083743959256142080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree053.table
  base := (4864008255905374602682467412996083184823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-9094942041123418379258702631136200000000000000)
      constant := (139702203995947537113340688214690846951778008920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179724326291326905781/50000000000000000000)
  centralHi := (359448652582653811563/100000000000000000000)
  directionLo := (362888430981859025821/100000000000000000000)
  directionHi := (181444215490929512911/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree054.table
  base := (13451526183376592544964846792100500131857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2165779)
      previous := (0)
      next := (1859165)
      square := (99683848796348617820051173732800000000000000)
      linear := (-6159454366406029353867568290368400000000000000)
      constant := (96217479736881754486957398411296529685784858208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree054.table
  base := (13451523716385177498102002333034049549821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1028463679416087252497247199412400000000000000)
      constant := (16094628381168268055860542648355835279356081104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (362888430981859025821/100000000000000000000)
  centralHi := (181444215490929512911/50000000000000000000)
  directionLo := (366295908846202600797/100000000000000000000)
  directionHi := (183147954423101300399/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree055.table
  base := (29572382426989648770131836391374120999171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 116640000000000000000000000000000000000000000
      center := (483273)
      previous := (0)
      next := (414855)
      square := (22243503450424898191251088353600000000000000)
      linear := (-1398361680686794624394742027531000000000000000)
      constant := (22247154174995866012053775310378518997334330544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree055.table
  base := (29572378484324842037053232670481483635267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6480000000000000000000000000000000000000000
      center := (26901)
      previous := (0)
      next := (22995)
      square := (1235750191690272121736171575200000000000000)
      linear := (-77829786680712001369353280647000000000000000)
      constant := (1240452907245816689074448307789534501395653016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366295908846202600797/100000000000000000000)
  centralHi := (183147954423101300399/50000000000000000000)
  directionLo := (7393439587484452227/2000000000000000000)
  directionHi := (369671979374222611351/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree056.table
  base := (16164017716460746173552247154390923886591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-172098258833241506549103226822555200000000000000)
      constant := (2787619761829111690512970373727193008163593776608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree056.table
  base := (16164016141722014587826054334429007101553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-9578635261987519058908269121862400000000000000)
      constant := (155431642866000041459802949640491019177637135248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7393439587484452227/2000000000000000000)
  centralHi := (369671979374222611351/100000000000000000000)
  directionLo := (37301749534230397923/10000000000000000000)
  directionHi := (373017495342303979231/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree057.table
  base := (7034001931501147649237343288821001453243/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-19443861589264540394049185368206600000000000000)
      constant := (320557141158021259574345350615890402069458771440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree057.table
  base := (8792501785610984305455179581118686161043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1082207370623209550236087920604200000000000000)
      constant := (17873575396217239256420596700640086475340026464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37301749534230397923/10000000000000000000)
  centralHi := (373017495342303979231/100000000000000000000)
  directionLo := (94083317905074128599/25000000000000000000)
  directionHi := (376333271620296514397/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree058.table
  base := (3809830374468751140030968521030221102129/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-177891249773520220543782109805163600000000000000)
      constant := (2984089179039878812830262984714697288711631513760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree058.table
  base := (38098301736865822683730061926923803097033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-9901097409230252845341313449013200000000000000)
      constant := (166386408772760993762248179029049291553232163464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94083317905074128599/25000000000000000000)
  centralHi := (376333271620296514397/100000000000000000000)
  directionLo := (23726255468084723091/6250000000000000000)
  directionHi := (379620087489355569457/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree059.table
  base := (20556458314787248960723818824792392846997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-180787745243659577541121551296467800000000000000)
      constant := (3084844486179244742644453028846346721030504267936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree059.table
  base := (8222583005433734629657273314875372718631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-10062328482851619738557835612588600000000000000)
      constant := (172004333404909231121905519264670003620612097240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23726255468084723091/6250000000000000000)
  centralHi := (379620087489355569457/100000000000000000000)
  directionLo := (382878688780684266477/100000000000000000000)
  directionHi := (191439344390342133239/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree060.table
  base := (44213847475791769127359680349055163024103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-20409360079310992726495665865308000000000000000)
      constant := (354142243406652932029507744051669934444787736048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree060.table
  base := (44213846197308285099017322194600298662369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1135951061830331847974928641796000000000000000)
      constant := (19746216933157274608604203347164357801946558728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382878688780684266477/100000000000000000000)
  centralHi := (191439344390342133239/50000000000000000000)
  directionLo := (386109789851806506927/100000000000000000000)
  directionHi := (24131861865737906683/6250000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree061.table
  base := (47401095626319153734022978031138112382897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-186580736183938291535800434279076200000000000000)
      constant := (3291396291554492273072935063138751219332927383568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree061.table
  base := (47401094606561233725489853190267889966421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-10384790630094353524990879939739400000000000000)
      constant := (183521265703041872536308675017041787216487137768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386109789851806506927/100000000000000000000)
  centralHi := (24131861865737906683/6250000000000000000)
  directionLo := (389314075415205462223/100000000000000000000)
  directionHi := (24332129713450341389/6250000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree062.table
  base := (25337330282454627286785136819267788050843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-189477231654077648533139875770380400000000000000)
      constant := (3397192788134489730558062682823236879117657925984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree062.table
  base := (10134931950347481898864758558285225722759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-10546021703715720418207402103314800000000000000)
      constant := (189420273279334304190224781826259189892350438360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389314075415205462223/100000000000000000000)
  centralHi := (24332129713450341389/6250000000000000000)
  directionLo := (392492202232587531879/100000000000000000000)
  directionHi := (9812305055814688297/2500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree063.table
  base := (54034541885808805877620457444962752285139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2165779)
      previous := (0)
      next := (1859165)
      square := (99683848796348617820051173732800000000000000)
      linear := (-7124952856452481686314048787469800000000000000)
      constant := (129802580734341160133271943947887136737448785808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree063.table
  base := (54034541237540787673021043010637307342463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1189694753037454145713769362987800000000000000)
      constant := (21712552788477599525773382187236934721567537656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392492202232587531879/100000000000000000000)
  centralHi := (9812305055814688297/2500000000000000000)
  directionLo := (395644800686646825287/100000000000000000000)
  directionHi := (49455600085830853161/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree064.table
  base := (28740369634998113875872196738107951990553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-195270222594356362527818758752988800000000000000)
      constant := (3613826966182407859539251279965522058788310066464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree064.table
  base := (57480738753321243010658342146345831097637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-10868483850958454204640446430465600000000000000)
      constant := (201499371129576692140841257490165883924703521896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395644800686646825287/100000000000000000000)
  centralHi := (49455600085830853161/12500000000000000000)
  directionLo := (398772476240984559811/100000000000000000000)
  directionHi := (99693119060246139953/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree065.table
  base := (61013252466532893186016875788856026090959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-198166718064495719525158200244293000000000000000)
      constant := (3724664646845918612782093183083908000537318438896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree065.table
  base := (61013252054839172446452574188327901201359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-11029714924579821097856968594041000000000000000)
      constant := (207679461360018854620077352681229976577396156472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398772476240984559811/100000000000000000000)
  centralHi := (99693119060246139953/25000000000000000000)
  directionLo := (40187581079775963333/10000000000000000000)
  directionHi := (401875810797759633331/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree066.table
  base := (12926416255585497649881557232068871547103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12960000000000000000000000000000000000000000
      center := (53697)
      previous := (0)
      next := (46095)
      square := (2471500383380544243472343150400000000000000)
      linear := (-184631050077718160259410139334800000000000000)
      constant := (3523583766335184024204033447911331287625227440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree066.table
  base := (64632080949961915098066429830658300457001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 720000000000000000000000000000000000000000
      center := (2989)
      previous := (0)
      next := (2555)
      square := (137305576854474680192907952800000000000000)
      linear := (-10276350778880797053327356067600000000000000)
      constant := (196467626972047883833982021588857397632904072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40187581079775963333/10000000000000000000)
  centralHi := (401875810797759633331/100000000000000000000)
  directionLo := (404955363961692451301/100000000000000000000)
  directionHi := (202477681980846225651/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree067.table
  base := (68337225548649738517966086719249314744857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-203959709004774433519837083226901400000000000000)
      constant := (3951381190042191508640952251446499636119265457808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree067.table
  base := (68337225287444085653296840054408406753323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-11352177071822554884290012921191800000000000000)
      constant := (220320724355341716594669245741636916856714549784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404955363961692451301/100000000000000000000)
  centralHi := (202477681980846225651/50000000000000000000)
  directionLo := (204005837109098979083/50000000000000000000)
  directionHi := (408011674218197958167/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree068.table
  base := (18032171289028919758984098498929571227813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-206856204474913790517176524718205600000000000000)
      constant := (4067260052182438788193857037169211927099786042688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree068.table
  base := (36064342474063394190362656449980835620753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-11513408145443921777506535084767200000000000000)
      constant := (226781897099020557221956764257773994718704002448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204005837109098979083/50000000000000000000)
  centralHi := (408011674218197958167/100000000000000000000)
  directionLo := (3211291094005250627/781250000000000000)
  directionHi := (411045260032672080257/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree069.table
  base := (7600646000361253584151677465762013545167/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-23305855549450349723835107356612200000000000000)
      constant := (464979923091473583084729043794097040410989082720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree069.table
  base := (15201291967606819349741558235038415617559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1297182135451698741191450805371400000000000000)
      constant := (25926307110692022547730647758039635884300870040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3211291094005250627/781250000000000000)
  centralHi := (411045260032672080257/100000000000000000000)
  directionLo := (82811324175457334731/20000000000000000000)
  directionHi := (51757077609660834207/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree070.table
  base := (79970550014745776750180628926748163345083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-212649195415192504511855407700814000000000000000)
      constant := (4304058956856842922715626812942110584848102821552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree070.table
  base := (79970549882957672256478583398803363258449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-11835870292686655563939579411918000000000000000)
      constant := (239985325041146126312358406097719624106368469192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82811324175457334731/20000000000000000000)
  centralHi := (51757077609660834207/12500000000000000000)
  directionLo := (83409247638210288211/20000000000000000000)
  directionHi := (13032694943470357533/3125000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree071.table
  base := (84020955129080736381984472324776316547511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-215545690885331861509194849192118200000000000000)
      constant := (4424978999197886710677062336397344986951430364784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree071.table
  base := (21005238756052156420697294285603369608901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-11997101366308022457156101575493400000000000000)
      constant := (246727580229172648944244839721378118517178838432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83409247638210288211/20000000000000000000)
  centralHi := (13032694943470357533/3125000000000000000)
  directionLo := (105003644069592090931/25000000000000000000)
  directionHi := (16800583051134734549/4000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree072.table
  base := (88157675298721729311403319976584845517111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2165779)
      previous := (0)
      next := (1859165)
      square := (99683848796348617820051173732800000000000000)
      linear := (-8090451346498934018760529284571200000000000000)
      constant := (168428867954770234199839475194777243044870426192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree072.table
  base := (22039418803821231552496969421193152402911/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1350925826658821038930291526563200000000000000)
      constant := (28173725506295737732542744068180938974936642528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105003644069592090931/25000000000000000000)
  centralHi := (16800583051134734549/4000000000000000000)
  directionLo := (422962083150827385901/100000000000000000000)
  directionHi := (211481041575413692951/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree073.table
  base := (23095177621406724514324007436875887690099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-221338681825610575503873732174726600000000000000)
      constant := (4671860263545881613566573630422118332594380332224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree073.table
  base := (18476142083851388438223508156981530479141/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-12319563513550756243589145902644200000000000000)
      constant := (260493173020717519700103361008824401709042437640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (422962083150827385901/100000000000000000000)
  centralHi := (211481041575413692951/50000000000000000000)
  directionLo := (425889191316564786451/100000000000000000000)
  directionHi := (106472297829141196613/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree074.table
  base := (9669006065950046586875746918010406818829/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-224235177295749932501213173666030800000000000000)
      constant := (4797821485456384818447056283623746521013133961760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree074.table
  base := (19338012121343254032866456464668790784591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-12480794587172123136805668066219600000000000000)
      constant := (267516510619034435167264420824926202739191055640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425889191316564786451/100000000000000000000)
  centralHi := (106472297829141196613/25000000000000000000)
  directionLo := (53599539815140266299/12500000000000000000)
  directionHi := (428796318521122130393/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree075.table
  base := (25271431449034535321953907150987167898453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-25236852529543254388728068350815000000000000000)
      constant := (547273677830682817390405971316395096134655222592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree075.table
  base := (101085725754166400461462377549441747507451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1404669517865943336669132247755000000000000000)
      constant := (30514838038863341296034002698187299004284913112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53599539815140266299/12500000000000000000)
  centralHi := (428796318521122130393/100000000000000000000)
  directionLo := (86336773688679780039/20000000000000000000)
  directionHi := (107920967110849725049/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree076.table
  base := (21113541175225632786499326739444040644957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-230028168236028646495892056648639200000000000000)
      constant := (5054785108577766556221829469412695650500080961040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree076.table
  base := (21113541168551991676162985140678109639737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-12803256734414856923238712393370400000000000000)
      constant := (281844268211446644235617834422327646103162493480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86336773688679780039/20000000000000000000)
  centralHi := (107920967110849725049/25000000000000000000)
  directionLo := (17382089253999259423/4000000000000000000)
  directionHi := (54319028918747685697/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree077.table
  base := (110136000883831467511412362977497267409551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 116640000000000000000000000000000000000000000
      center := (483273)
      previous := (0)
      next := (414855)
      square := (22243503450424898191251088353600000000000000)
      linear := (-1924997220712132260274640480495400000000000000)
      constant := (42857748014373357976823393300774209377065002864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree077.table
  base := (688350005358173764843709159193995290839/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6480000000000000000000000000000000000000000
      center := (26901)
      previous := (0)
      next := (22995)
      square := (1235750191690272121736171575200000000000000)
      linear := (-107144527339142345590539128569800000000000000)
      constant := (2389658580189034732816128838860595931754187520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17382089253999259423/4000000000000000000)
  centralHi := (54319028918747685697/12500000000000000000)
  directionLo := (437401784710851328397/100000000000000000000)
  directionHi := (218700892355425664199/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree078.table
  base := (22958122161316181126618777571847329066271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-26202351019589706721174548847916400000000000000)
      constant := (590941144882499659153148419804985778774281765680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree078.table
  base := (2295812215710027462141114282310159846003/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1458413209073065634407972968946800000000000000)
      constant := (32949644702564961938801813224251755628918906800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437401784710851328397/100000000000000000000)
  centralHi := (218700892355425664199/50000000000000000000)
  directionLo := (27514555861201394709/6250000000000000000)
  directionHi := (88046578755844463069/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree079.table
  base := (29882883908513102684026469534236560335303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-238717654646446717487910381122551800000000000000)
      constant := (5452833491173157596961518651292733637289471508928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree079.table
  base := (119531535617302324931522375893363282839269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-13286949955278957602888278884096600000000000000)
      constant := (304038610571293921965641282350077590780861403752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27514555861201394709/6250000000000000000)
  centralHi := (88046578755844463069/20000000000000000000)
  directionLo := (44304591213802903229/10000000000000000000)
  directionHi := (443045912138029032291/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree080.table
  base := (62179387678885549703269687655429352484689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-241614150116586074485249822613856000000000000000)
      constant := (5588877071419197333088259283412368568106301824032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree080.table
  base := (124358775344463383704205175354731034445833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-13448181028900324496104801047672000000000000000)
      constant := (311624112946854343948928965196093750948828873864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44304591213802903229/10000000000000000000)
  centralHi := (443045912138029032291/100000000000000000000)
  directionLo := (44584118221538064199/10000000000000000000)
  directionHi := (445841182215380641991/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree081.table
  base := (25854465994144659443189656448714311559689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2165779)
      previous := (0)
      next := (1859165)
      square := (99683848796348617820051173732800000000000000)
      linear := (-9055949836545386351207009781672600000000000000)
      constant := (212096334987804349386519142447610616219240317040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree081.table
  base := (646361649800760747790752774879871524679/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1512156900280187932146813690138600000000000000)
      constant := (35478145494358912065590141446444550644600689600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44584118221538064199/10000000000000000000)
  centralHi := (445841182215380641991/100000000000000000000)
  directionLo := (448619035771107629787/100000000000000000000)
  directionHi := (112154758942776907447/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree082.table
  base := (16784024933381462860064943154059838393197/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-247407141056864788479928705596464400000000000000)
      constant := (5866005410919451230981689488847236953457665814144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree082.table
  base := (67136099729327830696317541340897060396683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-13770643176143058282537845374822800000000000000)
      constant := (327076200077973574035802682953639163423166241328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448619035771107629787/100000000000000000000)
  centralHi := (112154758942776907447/25000000000000000000)
  directionLo := (28211237147272403577/6250000000000000000)
  directionHi := (451379794356358457233/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree083.table
  base := (69679191920907906876019088399186487978033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-250303636527004145477268147087768600000000000000)
      constant := (6007090170158425976955734878408765340627738012704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree083.table
  base := (13935838383514832288230306662884321972103/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-13931874249764425175754367538398200000000000000)
      constant := (334942784832706074928724705916955201671886520240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28211237147272403577/6250000000000000000)
  centralHi := (451379794356358457233/100000000000000000000)
  directionLo := (113530942437012120381/25000000000000000000)
  directionHi := (18164950789921939261/4000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree084.table
  base := (72265441545401790888597339484455534748021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-28133347999682611386067509842119200000000000000)
      constant := (683317258042410780290044774962643658274091322272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree084.table
  base := (144530883085509541422111812244752182595003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1565900591487310229885654411330400000000000000)
      constant := (38100340412567180427122350479102081014767666136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113530942437012120381/25000000000000000000)
  centralHi := (18164950789921939261/4000000000000000000)
  directionLo := (57106408044977844273/12500000000000000000)
  directionHi := (91370252871964550837/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree085.table
  base := (29957939442076657638837633171640557449623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-256096627467282859471947030070377000000000000000)
      constant := (6294300867584138763461538668122583885815903616560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree085.table
  base := (74894848603090187009290623103198613584889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-14254336397007158962187411865549000000000000000)
      constant := (350957036718890171179699242549410256287927953424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57106408044977844273/12500000000000000000)
  centralHi := (91370252871964550837/20000000000000000000)
  directionLo := (229781285815533049531/50000000000000000000)
  directionHi := (459562571631066099063/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree086.table
  base := (15513482619738699458647913801459844498911/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-258993122937422216469286471561681200000000000000)
      constant := (6440426805761280148632589435471049152744710463840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree086.table
  base := (77567413097025391093186736040621704525727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-14415567470628525855403934029124400000000000000)
      constant := (359104703849818865037960596845947583216906405232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229781285815533049531/50000000000000000000)
  centralHi := (459562571631066099063/100000000000000000000)
  directionLo := (28891123524711058623/6250000000000000000)
  directionHi := (462257976395376937969/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree087.table
  base := (2508847969515918552145031134629029715593/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-29098846489729063718513990339220600000000000000)
      constant := (732025904101019464690665179653355730378347640832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree087.table
  base := (160566270046370908253707575189209826852459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1619644282694432527624495132522200000000000000)
      constant := (40816229456186121619839579915921658511538622808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28891123524711058623/6250000000000000000)
  centralHi := (462257976395376937969/100000000000000000000)
  directionLo := (92987551045962913973/20000000000000000000)
  directionHi := (232468877614907284933/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree088.table
  base := (8304201438139124588878899417839289638237/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 116640000000000000000000000000000000000000000
      center := (483273)
      previous := (0)
      next := (414855)
      square := (22243503450424898191251088353600000000000000)
      linear := (-2188314990724801078214589706977600000000000000)
      constant := (55683635215076866967517839883633949486807927360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree088.table
  base := (166084028760681205451790363366921301642049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6480000000000000000000000000000000000000000
      center := (26901)
      previous := (0)
      next := (22995)
      square := (1235750191690272121736171575200000000000000)
      linear := (-121801897668357517701132052531200000000000000)
      constant := (3104802648646826542631723744878565003464047752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92987551045962913973/20000000000000000000)
  centralHi := (232468877614907284933/50000000000000000000)
  directionLo := (233801088393066012937/50000000000000000000)
  directionHi := (3740817414289056207/800000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree089.table
  base := (171688102336424677524983687934980045940033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-267682609347840287461304796035593800000000000000)
      constant := (6888886978103476945744010892655140359207189934352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree089.table
  base := (85844051167378683973420411693680463510677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-14899260691492626535053500519850600000000000000)
      constant := (384109869991417212905792556821877958065890324432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233801088393066012937/50000000000000000000)
  centralHi := (3740817414289056207/800000000000000000)
  directionLo := (94050300421023466609/20000000000000000000)
  directionHi := (235125751052558666523/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree090.table
  base := (22172311345986209407801189751149944584257/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 522720000000000000000000000000000000000000000
      center := (2165779)
      previous := (0)
      next := (1859165)
      square := (99683848796348617820051173732800000000000000)
      linear := (-10021448326591838683653490278774000000000000000)
      constant := (260804981042363039025273516677341254226466255232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree090.table
  base := (35475698153313376119597335543128138284117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1673387973901554825363335853714000000000000000)
      constant := (43625812624552148097050295197894911703656136520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94050300421023466609/20000000000000000000)
  centralHi := (235125751052558666523/50000000000000000000)
  directionLo := (472885984915084234899/100000000000000000000)
  directionHi := (4728859849150842349/1000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree091.table
  base := (183155194055284030547657369434256104046993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-273475600288119001455983679018202200000000000000)
      constant := (7196262391142603911318511150665521878160099288592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree091.table
  base := (183155194054234693480213294397753982460843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-15221722838735360321486544847001400000000000000)
      constant := (401248451374775352646898325745585356756789777944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (472885984915084234899/100000000000000000000)
  centralHi := (4728859849150842349/1000000000000000000)
  directionLo := (237752935957739214631/50000000000000000000)
  directionHi := (475505871915478429263/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree092.table
  base := (37803642439369674760936599904785834625227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-276372095758258358453323120509506400000000000000)
      constant := (7352470687097399442957456908137323194916531875440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree092.table
  base := (9450910609800803185988074849527517118929/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-15382953912356727214703067010576800000000000000)
      constant := (409958283252698470426883854208916871245219700640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237752935957739214631/50000000000000000000)
  centralHi := (475505871915478429263/100000000000000000000)
  directionLo := (478111403046496560617/100000000000000000000)
  directionHi := (239055701523248280309/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree093.table
  base := (97483772595467560045717716748605890399367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-31029843469821968383406951333423400000000000000)
      constant := (834484375111762593275196470194699143867734270944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree093.table
  base := (9748377259513751440543260973777331350751/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1727131665108677123102176574905800000000000000)
      constant := (46529089917178934851695237385185724714554854240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478111403046496560617/100000000000000000000)
  centralHi := (239055701523248280309/50000000000000000000)
  directionLo := (240351405872775988489/50000000000000000000)
  directionHi := (480702811745551976979/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree094.table
  base := (40200638607198150640828104080016012982229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-282165086698537072448002003492114800000000000000)
      constant := (7669928457865803055103345696206373324131955028880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree094.table
  base := (100501596517733653153749478423042213293377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-15705416059599461001136111337727600000000000000)
      constant := (427659029380390098263990204722287237719814207632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240351405872775988489/50000000000000000000)
  centralHi := (480702811745551976979/100000000000000000000)
  directionLo := (483280325191363120079/100000000000000000000)
  directionHi := (6041004064892039001/1250000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree095.table
  base := (207125155730541716282038399225226968428041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-285061582168676429445341444983419000000000000000)
      constant := (7831177932675138894203097036226069511779105097104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree095.table
  base := (25890644466265834276586534521627687080721/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-15866647133220827894352633501303000000000000000)
      constant := (436649943629922560688744601270655832009001377344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483280325191363120079/100000000000000000000)
  centralHi := (6041004064892039001/1250000000000000000)
  directionLo := (485844164536386903609/100000000000000000000)
  directionHi := (48584416453638690361/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree096.table
  base := (213333433273183141108209186519300583801241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1568160000000000000000000000000000000000000000
      center := (6497337)
      previous := (0)
      next := (5577495)
      square := (299051546389045853460153521198400000000000000)
      linear := (-31995341959868420715853431830524800000000000000)
      constant := (888234200047987567160809075090977040349375408656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree096.table
  base := (13333339579553380618426150331914380301959/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (361669)
      previous := (0)
      next := (309155)
      square := (16613974799391436303341862288800000000000000)
      linear := (-1780875356315799420841017296097600000000000000)
      constant := (49526061333677567200539970462375009299050668928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485844164536386903609/100000000000000000000)
  centralHi := (48584416453638690361/10000000000000000000)
  directionLo := (122098636282067533599/25000000000000000000)
  directionHi := (488394545128270134397/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree097.table
  base := (219628025662569813151398414610752673696773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-290854573108955143440020327966027400000000000000)
      constant := (8158718061134152125378500809563111302755898392912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree097.table
  base := (109814012831154482501769147833699957218417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-16189109280463561680785677828453800000000000000)
      constant := (454912854499811617760962219272481854991163280272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell182.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122098636282067533599/25000000000000000000)
  centralHi := (488394545128270134397/100000000000000000000)
  directionLo := (490931676720946573631/100000000000000000000)
  directionHi := (7670807448764790213/1562500000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree098.table
  base := (226008932897408898784126398497067840932689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14113440000000000000000000000000000000000000000
      center := (58476033)
      previous := (0)
      next := (50197455)
      square := (2691463917501412681141381690785600000000000000)
      linear := (-293751068579094500437359769457331600000000000000)
      constant := (8325008714780106324013612748908833239893305024016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree098.table
  base := (226008932897202139095835108395177946429293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3255021)
      previous := (0)
      next := (2782395)
      square := (149525773194522926730076760599200000000000000)
      linear := (-16350340354084928574002199992029200000000000000)
      constant := (464184851119962019065035992303570162423628005544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell182.Kernel098
