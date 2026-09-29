import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell027.Parameters
import ForestUnimodality.BinomialMassData.Q301_666.Batch000_049
import ForestUnimodality.BinomialMassData.Q301_666.Batch050_099
import ForestUnimodality.BinomialMassData.Q301_666.Batch100_149
import ForestUnimodality.BinomialMassData.Q17_37.Batch000_049
import ForestUnimodality.BinomialMassData.Q17_37.Batch050_099
import ForestUnimodality.BinomialMassData.Q17_37.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree000.table
  base := (1789135476460110426632610371/50000000000000000000000000)
  polynomial :=
    { denominator := 6660000000000000000000000000000000000000000
      center := (28835)
      previous := (23779)
      next := (0)
      square := (646986765355764542606564759340000000000000)
      linear := (2780234370157552249436250233400000000000000)
      constant := (238312845464486708827463701417200000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree000.table
  base := (1789135476460110426632610371/50000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1580)
      previous := (1343)
      next := (0)
      square := (35943709186431363478142486630000000000000)
      linear := (154457465008752902746458346300000000000000)
      constant := (13239602525804817157081316745400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree001.table
  base := (109303093469849464260929328782146836588841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (731075028890379771737695335160860000000000000)
      constant := (48107624897593024761079035148939717249999958596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree001.table
  base := (216307582187300323017883049470374754258763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (4492840092985191043362114267680000000000000)
      constant := (293780052621559360811959215773953038580246547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49768603062450172227/100000000000000000000)
  directionHi := (12442150765612543057/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree002.table
  base := (27780964862467615705993333612122144206143/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (536332012518294644413119342599520000000000000)
      constant := (30145212553681040772732322195982704488749911270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree002.table
  base := (136301466535048384889881836543305781293681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (3270753980646524685105269722260000000000000)
      constant := (182468151925359712009537102198025614591049289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768603062450172227/100000000000000000000)
  centralHi := (12442150765612543057/25000000000000000000)
  directionLo := (70383433431280185901/100000000000000000000)
  directionHi := (35191716715640092951/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree003.table
  base := (2884772407445907971215901843882503561389/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (37954332905134390787615927782020000000000000)
      constant := (2179302125543309588972841668646079888311927616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree003.table
  base := (45028591770146844247131994894389933723833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (2048667868307858326848425176840000000000000)
      constant := (117937699161861823033082042784529638535854754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70383433431280185901/100000000000000000000)
  centralHi := (35191716715640092951/50000000000000000000)
  directionLo := (17240349825178344083/20000000000000000000)
  directionHi := (2693804660184116263/3125000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree004.table
  base := (16059508271909616695847058995112179080587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (146845979774124389763967357476840000000000000)
      constant := (13276997302302435910500396787125075408537694744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree004.table
  base := (62452115219659067153342572875908886312769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (826581755969191968591580631420000000000000)
      constant := (79485830311822352700840621696479265362180761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17240349825178344083/20000000000000000000)
  centralHi := (2693804660184116263/3125000000000000000)
  directionLo := (49768603062450172227/50000000000000000000)
  directionHi := (19907441224980068891/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree005.table
  base := (23308337575897312360254566395425224594069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-47897036597960737560608635084500000000000000)
      constant := (9346607698000835336024832445768105920046869364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree005.table
  base := (45241249557809033038847355702307941140227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-395504356369474389665263914000000000000000)
      constant := (55825123926247018175910893923709571420970763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768603062450172227/50000000000000000000)
  centralHi := (19907441224980068891/20000000000000000000)
  directionLo := (11128597959284279629/10000000000000000000)
  directionHi := (111285979592842796291/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree006.table
  base := (35000173323366682017878780017657052048969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-26960005885560651653909403071760000000000000)
      constant := (759553061985343655518150930867285076590694098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree006.table
  base := (8484002528992956349885612369714626838981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-1617590468708140747922108459420000000000000)
      constant := (40810718860457278989850927713917296570259956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11128597959284279629/10000000000000000000)
  centralHi := (111285979592842796291/100000000000000000000)
  directionLo := (15238460339264895269/12500000000000000000)
  directionHi := (121907682714119162153/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree007.table
  base := (13456276690881166068179128023115500143001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-437383069342130992209760620207180000000000000)
      constant := (5195990271209688041778822825386373781428951556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree007.table
  base := (26070010149418485917334146495570355378143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-2839676581046807106178953004840000000000000)
      constant := (31066131660919191205190437212125816512677767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15238460339264895269/12500000000000000000)
  centralHi := (121907682714119162153/100000000000000000000)
  directionLo := (65837673401165370751/50000000000000000000)
  directionHi := (131675346802330741503/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree008.table
  base := (838610774468466276839581264300770431247/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-632126085714216119534336612768520000000000000)
      constant := (4118696890939988853800943973278486617527429150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree008.table
  base := (20276734409381039436306778564720261506689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-4061762693385473464435797550260000000000000)
      constant := (24720602952069396833480872669342038002657241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65837673401165370751/50000000000000000000)
  centralHi := (131675346802330741503/100000000000000000000)
  directionLo := (70383433431280185901/50000000000000000000)
  directionHi := (140766866862560371803/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree009.table
  base := (8185243819794955029917646971439769939027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-91874344676255694095434733925540000000000000)
      constant := (381041472408749594240098719166192621675006668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree009.table
  base := (986828743621371413827858292020659802027/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-5283848805724139822692642095680000000000000)
      constant := (20724215149758779048813428869430532303599408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70383433431280185901/50000000000000000000)
  centralHi := (140766866862560371803/100000000000000000000)
  directionLo := (149305809187350516681/100000000000000000000)
  directionHi := (74652904593675258341/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree010.table
  base := (6336723310855245399578226218924172012949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-1021612118458386374183488597891200000000000000)
      constant := (3027163236701333582895908284743630041375606644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree010.table
  base := (380277470274759212557087736419278510093/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-6505934918062806180949486641100000000000000)
      constant := (18476377595710452833514274297055752970154144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149305809187350516681/100000000000000000000)
  centralHi := (74652904593675258341/50000000000000000000)
  directionLo := (78691070821086884317/50000000000000000000)
  directionHi := (31476428328434753727/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree011.table
  base := (9605145605209536531505932258909578599193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-1216355134830471501508064590452540000000000000)
      constant := (2852408408128008836651606047594643522571825154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree011.table
  base := (228943292310127170314636532271711591207/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-7728021030401472539206331186520000000000000)
      constant := (17624079717841942640062451018408926734495320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78691070821086884317/50000000000000000000)
  centralHi := (31476428328434753727/20000000000000000000)
  directionLo := (165063782698279913367/100000000000000000000)
  directionHi := (20632972837284989171/12500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree012.table
  base := (7001122235922905853403932305107088136117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-156788683466950736536960064779320000000000000)
      constant := (318737181552995239694115381386768865850195114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree012.table
  base := (1319724088813554869504299660858946475043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-8950107142740138897463175731940000000000000)
      constant := (17952118296481775313543691333219488621669335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165063782698279913367/100000000000000000000)
  centralHi := (20632972837284989171/12500000000000000000)
  directionLo := (172403498251783440831/100000000000000000000)
  directionHi := (2693804660184116263/1562500000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree013.table
  base := (4756542241166864218892665642285043240033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-1605841167574641756157216575575220000000000000)
      constant := (3052591978920925264548779368719247319688038674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree013.table
  base := (439124086785710264186018051835371136303/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-10172193255078805255720020277360000000000000)
      constant := (19323176558851015080981378799916230855988070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172403498251783440831/100000000000000000000)
  centralHi := (2693804660184116263/1562500000000000000)
  directionLo := (179443250249878222051/100000000000000000000)
  directionHi := (44860812562469555513/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree014.table
  base := (175078541286826919515852948736861251161/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-1800584183946726883481792568136560000000000000)
      constant := (3388722946830927179430614669874637832959748128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree014.table
  base := (1234083621600811246577180720428888097789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-11394279367417471613976864822780000000000000)
      constant := (21644948693487347984225369870694295611746282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179443250249878222051/100000000000000000000)
  centralHi := (44860812562469555513/25000000000000000000)
  directionLo := (186217061278036887783/100000000000000000000)
  directionHi := (23277132659754610973/12500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree015.table
  base := (67865837932666650177536421581482727981/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-221703022257645778978485395633100000000000000)
      constant := (429563224868554112059074500777649358126524832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree015.table
  base := (781572470569760956936540188255028570049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-12616365479756137972233709368200000000000000)
      constant := (24851959401132050662299655835971134112397081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186217061278036887783/100000000000000000000)
  centralHi := (23277132659754610973/12500000000000000000)
  directionLo := (192752970824876963617/100000000000000000000)
  directionHi := (96376485412438481809/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree016.table
  base := (-426224703046512894431881922484309215387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-2190070216690897138130944553259240000000000000)
      constant := (4476522630900340300652087182726794870829901914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree016.table
  base := (-88025656594846452200200446187834903427/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-13838451592094804330490553913620000000000000)
      constant := (28895387673861046583247646163910832137667496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192752970824876963617/100000000000000000000)
  centralHi := (96376485412438481809/50000000000000000000)
  directionLo := (49768603062450172227/25000000000000000000)
  directionHi := (199074412249800688909/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree017.table
  base := (-881601665931491961344488612868066199689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-2384813233062982265455520545820580000000000000)
      constant := (5213823937093153737055037348927847028730745916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree017.table
  base := (-201689858061231577480887531269195238949/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-15060537704433470688747398459040000000000000)
      constant := (33737267508583337541855826152014717178788190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768603062450172227/25000000000000000000)
  centralHi := (199074412249800688909/100000000000000000000)
  directionLo := (102600603632960317061/50000000000000000000)
  directionHi := (205201207265920634123/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree018.table
  base := (-2947630883409665576719503559000691917807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-286617361048340821420010726486880000000000000)
      constant := (674774689164342370121338936855524949761399906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree018.table
  base := (-1589394045220645078669983180836334066263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-16282623816772137047004243004460000000000000)
      constant := (39347096794769300416329923382710117326571906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102600603632960317061/50000000000000000000)
  centralHi := (205201207265920634123/100000000000000000000)
  directionLo := (211150300293840557703/100000000000000000000)
  directionHi := (26393787536730069713/12500000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree019.table
  base := (-3997984217396294907766930350515916363321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-2774299265807152520104672530943260000000000000)
      constant := (7049869666065417019012452268186676100775395262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree019.table
  base := (-526025287364332420310935640896056156649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-17504709929110803405261087549880000000000000)
      constant := (45699783793099122672976356941716392972380152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211150300293840557703/100000000000000000000)
  centralHi := (26393787536730069713/12500000000000000000)
  directionLo := (108468155655204593059/50000000000000000000)
  directionHi := (216936311310409186119/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree020.table
  base := (-4929679020412754194707922431207953794827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-2969042282179237647429248523504600000000000000)
      constant := (8141097467711629888771533885515562423290857594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree020.table
  base := (-1280116787499537319944566669191419397737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-18726796041449469763517932095300000000000000)
      constant := (52774347286283725569032889621507787377992188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108468155655204593059/50000000000000000000)
  centralHi := (216936311310409186119/100000000000000000000)
  directionLo := (11128597959284279629/5000000000000000000)
  directionHi := (222571959185685592581/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree021.table
  base := (-5755736123065213867655000204396137158141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-351531699839035863861536057340660000000000000)
      constant := (1038196430405282741635533414853225388149089478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree021.table
  base := (-2964269359322825278977797909901724078167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-19948882153788136121774776640720000000000000)
      constant := (60553050407711232806369964518099079473978754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11128597959284279629/5000000000000000000)
  centralHi := (222571959185685592581/100000000000000000000)
  directionLo := (57017097691472236303/25000000000000000000)
  directionHi := (228068390765888945213/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree022.table
  base := (-648724394558470206579330118713938995337/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-3358528314923407902078400508627280000000000000)
      constant := (10655421716211164418205051384418780374921508140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree022.table
  base := (-3321724086644241787365400480830025831543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-21170968266126802480031621186140000000000000)
      constant := (69020791487799166787900773044527389273235266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57017097691472236303/25000000000000000000)
  centralHi := (228068390765888945213/100000000000000000000)
  directionLo := (233435440148512887617/100000000000000000000)
  directionHi := (116717720074256443809/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree023.table
  base := (-1426739200236382396095256174906110740559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-3553271331295493029402976501188620000000000000)
      constant := (12073953543029648004635299184944117860901530490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree023.table
  base := (-7274631048515440239262193409435168726509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-22393054378465468838288465731560000000000000)
      constant := (78164653279695471389987587021373254013409179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233435440148512887617/100000000000000000000)
  centralHi := (116717720074256443809/50000000000000000000)
  directionLo := (119340917719068244159/50000000000000000000)
  directionHi := (238681835438136488319/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree024.table
  base := (-1925812129529025514198184337211965663409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-416446038629730906303061388194440000000000000)
      constant := (1510839386901345957175071186018170968489101688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree024.table
  base := (-24469317948856763878550706543134466877/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-23615140490804135196545310276980000000000000)
      constant := (87973554550747982127786552386543652750523840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119340917719068244159/50000000000000000000)
  centralHi := (238681835438136488319/100000000000000000000)
  directionLo := (48763073085647664861/20000000000000000000)
  directionHi := (121907682714119162153/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree025.table
  base := (-8202924428654970628166140552108083171103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-3942757364039663284052128486311300000000000000)
      constant := (15224667001586095647036085535276448530479118866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree025.table
  base := (-4158528527645339547671552519766154589881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-24837226603142801554802154822400000000000000)
      constant := (98437971446348293630676077092130268732905822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48763073085647664861/20000000000000000000)
  centralHi := (121907682714119162153/50000000000000000000)
  directionLo := (49768603062450172227/20000000000000000000)
  directionHi := (15552688457015678821/6250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree026.table
  base := (-8638779448976981828378195213145171362483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-4137500380411748411376704478872640000000000000)
      constant := (16953948076828966683354794856931510185571245226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree026.table
  base := (-4370621534528542850941543842765139084737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-26059312715481467913058999367820000000000000)
      constant := (109549709015348198945155808704269049185990094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768603062450172227/20000000000000000000)
  centralHi := (15552688457015678821/6250000000000000000)
  directionLo := (253771078179687058683/100000000000000000000)
  directionHi := (63442769544921764671/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree027.table
  base := (-9016040023239096602195008425836215381667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-481360377420425948744586719048220000000000000)
      constant := (2087137621945387137680381215562538980564961786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree027.table
  base := (-910789440691781563067038195278807389621/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-27281398827820134271315843913240000000000000)
      constant := (121301710580251011525813196579123126836088510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253771078179687058683/100000000000000000000)
  centralHi := (63442769544921764671/25000000000000000000)
  directionLo := (258605247377675161247/100000000000000000000)
  directionHi := (8081413980552348789/3125000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree028.table
  base := (-9339219486265674347647236235883466412859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-4526986413155918666025856463995320000000000000)
      constant := (20714537605253971535765550948166716585888956698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree028.table
  base := (-9421451774265023309689608046984010335053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-28503484940158800629572688458660000000000000)
      constant := (133687896815374871960737295655118889851312443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258605247377675161247/100000000000000000000)
  centralHi := (8081413980552348789/3125000000000000000)
  directionLo := (65837673401165370751/25000000000000000000)
  directionHi := (52670138720932296601/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree029.table
  base := (-4806108394997557348426703031474600079889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-4721729429528003793350432456556660000000000000)
      constant := (22743980398302434179669172107165247286964754716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree029.table
  base := (-9685741950464740199060011599356264489569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-29725571052497466987829533004080000000000000)
      constant := (146703028859767683181024858663091273913780039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65837673401165370751/25000000000000000000)
  centralHi := (52670138720932296601/20000000000000000000)
  directionLo := (268012129712153168409/100000000000000000000)
  directionHi := (26801212971215316841/10000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree030.table
  base := (-9838400920536682525848395170523903306639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-546274716211120991186112049902000000000000000)
      constant := (2763535534405836847239670156368449974717801762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree030.table
  base := (-1238007908239613275837314891286572361833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-30947657164836133346086377549500000000000000)
      constant := (160342591299111927452737613196629459493204984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268012129712153168409/100000000000000000000)
  centralHi := (26801212971215316841/10000000000000000000)
  directionLo := (54518773105649301597/20000000000000000000)
  directionHi := (136296932764123253993/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree031.table
  base := (-10020683363894179079356318636332346859253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-5111215462272174047999584441679340000000000000)
      constant := (27097410135761312839776704054911479778248588166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree031.table
  base := (-403170356106764289232144631498327817743/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-32169743277174799704343222094920000000000000)
      constant := (174602691817184459681241833088579730437745825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54518773105649301597/20000000000000000000)
  centralHi := (136296932764123253993/50000000000000000000)
  directionLo := (277099854518943160901/100000000000000000000)
  directionHi := (138549927259471580451/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree032.table
  base := (-2540395117426582193431864772005379484399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-5305958478644259175324160434240680000000000000)
      constant := (29420193305638600799918857069357243794835834312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree032.table
  base := (-10213779878712499873209604946399213140251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-33391829389513466062600066640340000000000000)
      constant := (189479974970355386478626357017819477210996381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277099854518943160901/100000000000000000000)
  centralHi := (138549927259471580451/50000000000000000000)
  directionLo := (70383433431280185901/25000000000000000000)
  directionHi := (56306746745024148721/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree033.table
  base := (-10263267208048236541889117615592132267217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-611189055001816033627637380755780000000000000)
      constant := (3537742995419008764863193274390573676671238686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree033.table
  base := (-10309739236052910042685096903996495231261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-34613915501852132420856911185760000000000000)
      constant := (204971548004118732175786957487918798028403691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70383433431280185901/25000000000000000000)
  centralHi := (56306746745024148721/20000000000000000000)
  directionLo := (14294942906146469971/5000000000000000000)
  directionHi := (285898858122929399421/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree034.table
  base := (-10327623554893478105815954635292762048781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-5695444511388429429973312419363360000000000000)
      constant := (34355474157847279414858255017590461818345447382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree034.table
  base := (-1296119837242884207309167898060318619351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-35836001614190798779113755731180000000000000)
      constant := (221074916979341501299279623162203390480867848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14294942906146469971/5000000000000000000)
  centralHi := (285898858122929399421/100000000000000000000)
  directionLo := (290198330330797455631/100000000000000000000)
  directionHi := (18137395645674840977/6250000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree035.table
  base := (-1294534317903540441262796066918925573823/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-5890187527760514557297888411924700000000000000)
      constant := (36967194506301573390801787227838711192709461648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree035.table
  base := (-2598252215461517394162674384107032668603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-37058087726529465137370600276600000000000000)
      constant := (237787931748096738895135825758879889106729972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290198330330797455631/100000000000000000000)
  centralHi := (18137395645674840977/6250000000000000000)
  directionLo := (147217513205435550819/50000000000000000000)
  directionHi := (294435026410871101639/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree036.table
  base := (-10350624859190289239985283690407210979251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-676103393792511076069162711609560000000000000)
      constant := (4408281830627972743760349054033465507049296858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree036.table
  base := (-5191621917258561392000899534893191833701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-38280173838868131495627444822020000000000000)
      constant := (255108738538236541956447394336422440759326662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147217513205435550819/50000000000000000000)
  centralHi := (294435026410871101639/100000000000000000000)
  directionLo := (149305809187350516681/50000000000000000000)
  directionHi := (298611618374701033363/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree037.table
  base := (-1288986091757241021007011367720250904593/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59940000000000000000000000000000000000000000
      center := (259515)
      previous := (214011)
      next := (0)
      square := (5822880888201880883459082834060000000000000)
      linear := (-169720907040667157079649740460740000000000000)
      constant := (1148033264219279146262109846350693528622956464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree037.table
  base := (-5170415541776264801581382107612017168067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1580)
      previous := (1343)
      next := (0)
      square := (35943709186431363478142486630000000000000)
      linear := (-1067628647329913455510386199120000000000000)
      constant := (7379344299638421103176364473006710729563042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149305809187350516681/50000000000000000000)
  centralHi := (298611618374701033363/100000000000000000000)
  directionLo := (302730593893557134941/100000000000000000000)
  directionHi := (151365296946778567471/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree038.table
  base := (-409644631040866046791829302540913695577/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-6474416576876769939271616389608720000000000000)
      constant := (45375044627681041605659703298195211060558102350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree038.table
  base := (-2566694292297738675874258443847886435239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-40724346063545464212141133912860000000000000)
      constant := (291567555412285123546011548794528973880631236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302730593893557134941/100000000000000000000)
  centralHi := (151365296946778567471/50000000000000000000)
  directionLo := (306794273626372526433/100000000000000000000)
  directionHi := (153397136813186263217/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree039.table
  base := (-2534803323893081170635392776327044535121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-741017732583206118510688042463340000000000000)
      constant := (5374197423205427877665361427158950874262193272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree039.table
  base := (-10161949926596324932529707405874955815989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-41946432175884130570397978458280000000000000)
      constant := (310702999448887754287643722787767185487911059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306794273626372526433/100000000000000000000)
  centralHi := (153397136813186263217/50000000000000000000)
  directionLo := (3108048265080857167/1000000000000000000)
  directionHi := (310804826508085716701/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree040.table
  base := (-10006965601731226493442996553837573416961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-6863902609620940193920768374731400000000000000)
      constant := (51455253377130635346605295541207010642733223342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree040.table
  base := (-313346799660767296919043487649318804411/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-43168518288222796928654823003700000000000000)
      constant := (330441046864937847856359565185058641816362912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3108048265080857167/1000000000000000000)
  centralHi := (310804826508085716701/100000000000000000000)
  directionLo := (314764283284347537269/100000000000000000000)
  directionHi := (31476428328434753727/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree041.table
  base := (-246126267020279420140224254875080721993/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-7058645625993025321245344367292740000000000000)
      constant := (54637323970077910309505732172461968905513457840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree041.table
  base := (-9862865275029843521733725651497099299263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-44390604400561463286911667549120000000000000)
      constant := (350780814493627540192381907812910471059308953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314764283284347537269/100000000000000000000)
  centralHi := (31476428328434753727/10000000000000000000)
  directionLo := (63734909706469879371/20000000000000000000)
  directionHi := (39834318566543674607/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree042.table
  base := (-4827027306564219228926313286380206619719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-805932071373901160952213373317120000000000000)
      constant := (6434873178663366183091473709478457896953768804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree042.table
  base := (-9669809200977878803378522753010455682963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-45612690512900129645168512094540000000000000)
      constant := (371721540874259370159990762390968686170023653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63734909706469879371/20000000000000000000)
  centralHi := (39834318566543674607/12500000000000000000)
  directionLo := (20158588210607931293/6250000000000000000)
  directionHi := (322537411369726900689/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree043.table
  base := (-471724201732531004641308293631446167271/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-7448131658737195575894496352415420000000000000)
      constant := (61284744930096167052007769526995257638299443240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree043.table
  base := (-4724204468270419018490332893909599186773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-46834776625238796003425356639960000000000000)
      constant := (393262569476116405131704236258565517426615526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20158588210607931293/6250000000000000000)
  centralHi := (322537411369726900689/100000000000000000000)
  directionLo := (326354555022405287783/100000000000000000000)
  directionHi := (40794319377800660973/12500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree044.table
  base := (-9186776908810975784723661520063956707649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-7642874675109280703219072344976760000000000000)
      constant := (64749885805801224299992637381378775809291020078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree044.table
  base := (-9199077969151411695286300524837119934997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-48056862737577462361682201185380000000000000)
      constant := (415403334234903291850332855858057982808989107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326354555022405287783/100000000000000000000)
  centralHi := (40794319377800660973/12500000000000000000)
  directionLo := (165063782698279913367/50000000000000000000)
  directionHi := (66025513079311965347/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree045.table
  base := (-4455655918843596860221957254645552493857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-870846410164596203393738704170900000000000000)
      constant := (7589910807719320206784869406839923590892751612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree045.table
  base := (-8922172812825854588275904023331172731043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-49278948849916128719939045730800000000000000)
      constant := (438143347082931777481013348095309624531202133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165063782698279913367/50000000000000000000)
  centralHi := (66025513079311965347/20000000000000000000)
  directionLo := (33385793877852838887/10000000000000000000)
  directionHi := (333857938778528388871/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree046.table
  base := (-430420805531454168914533884231693669717/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-8032360707853450957868224330099440000000000000)
      constant := (71962606735536717688742081669228488826350063480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree046.table
  base := (-861800086128113189467050594651321444461/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-50501034962254795078195890276220000000000000)
      constant := (461482187198203336694076623361383409425328910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33385793877852838887/10000000000000000000)
  centralHi := (333857938778528388871/100000000000000000000)
  directionLo := (84386772192178961207/25000000000000000000)
  directionHi := (337547088768715844829/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree047.table
  base := (-4139186330771166847945113129744820077259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-8227103724225536085192800322660780000000000000)
      constant := (75710051455473995901818528340109461585811306996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree047.table
  base := (-51792669740913607296972553014917561623/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-51723121074593461436452734821640000000000000)
      constant := (485419491735442359455403389160902457302098080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84386772192178961207/25000000000000000000)
  centralHi := (337547088768715844829/100000000000000000000)
  directionLo := (341196352540620016363/100000000000000000000)
  directionHi := (85299088135155004091/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree048.table
  base := (-247544565087875460034193011651997669213/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-935760748955291245835264035024680000000000000)
      constant := (8839053020452860048357858772236207149928104128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree048.table
  base := (-247777507383889879022927944157272506829/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-52945207186932127794709579367060000000000000)
      constant := (509954947834801533811681766838998206020835168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341196352540620016363/100000000000000000000)
  centralHi := (85299088135155004091/25000000000000000000)
  directionLo := (344806996503566881663/100000000000000000000)
  directionHi := (2693804660184116263/781250000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree049.table
  base := (-7537787823779835795843173503070900499583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-8616589756969706339841952307783460000000000000)
      constant := (83486837026529845674511771026388136829003481426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree049.table
  base := (-3772178573237369716121492207638368264851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-54167293299270794152966423912480000000000000)
      constant := (535088285732122004877697711467696147690837962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344806996503566881663/100000000000000000000)
  centralHi := (2693804660184116263/781250000000000000)
  directionLo := (348380221437151205589/100000000000000000000)
  directionHi := (34838022143715120559/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree050.table
  base := (-1425528136868662352993223599879419757889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-8811332773341791467166528300344800000000000000)
      constant := (87516090441840640572435190707232210224674466790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree050.table
  base := (-445839237522682730006062275553163527499/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-55389379411609460511223268457900000000000000)
      constant := (560819272818908058065239957836283506093661904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348380221437151205589/100000000000000000000)
  centralHi := (34838022143715120559/10000000000000000000)
  directionLo := (70383433431280185901/20000000000000000000)
  directionHi := (175958583578200464753/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree051.table
  base := (-6691142699252318664413149237805392271147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1000675087745986288276789365878460000000000000)
      constant := (10182133597930818569054448664681754523654395626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree051.table
  base := (-669623870931043478568807576367921085473/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-56611465523948126869480113003320000000000000)
      constant := (587147708521105928678874384859533160339874630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70383433431280185901/20000000000000000000)
  centralHi := (175958583578200464753/50000000000000000000)
  directionLo := (88854729189761601337/25000000000000000000)
  directionHi := (355418916759046405349/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree052.table
  base := (-622843049571929625846993126024716209661/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-9200818806085961721815680285467480000000000000)
      constant := (95856142544230104855632566851202984884538027420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree052.table
  base := (-1246583241996510988318142970749185067837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-57833551636286793227736957548740000000000000)
      constant := (614073419883820845396966512477461828210655735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88854729189761601337/25000000000000000000)
  centralHi := (355418916759046405349/100000000000000000000)
  directionLo := (358886500499756444103/100000000000000000000)
  directionHi := (44860812562469555513/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree053.table
  base := (-1147924439151502813316117074238089122091/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-9395561822458046849140256278028820000000000000)
      constant := (100166884733534994887379498979771480353404511010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree053.table
  base := (-1148713848991451032021345909419781279229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-59055637748625459585993802094160000000000000)
      constant := (641596257764663565903675154766711597143677495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358886500499756444103/100000000000000000000)
  centralHi := (44860812562469555513/12500000000000000000)
  directionLo := (72464179866124037177/20000000000000000000)
  directionHi := (181160449665310092943/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree054.table
  base := (-5224819924978904372437844144331992444103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1065589426536681330718314696732240000000000000)
      constant := (11619045144453119344302003058123551042192413874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree054.table
  base := (-5228291760037054499402584014468373755073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-60277723860964125944250646639580000000000000)
      constant := (669716093551830441608370422277552796329305063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72464179866124037177/20000000000000000000)
  centralHi := (181160449665310092943/50000000000000000000)
  directionLo := (365723048142357486457/100000000000000000000)
  directionHi := (182861524071178743229/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree055.table
  base := (-4684111981212949047370361361410691481183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-9785047855202217103789408263151500000000000000)
      constant := (109069687661343315659188626302817934664686196626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree055.table
  base := (-146473899096859988645496623495283246739/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-61499809973302792302507491185000000000000000)
      constant := (698432816334585083729996161860168631526857888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365723048142357486457/100000000000000000000)
  centralHi := (182861524071178743229/50000000000000000000)
  directionLo := (73818767747321509021/20000000000000000000)
  directionHi := (184546919368303772553/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree056.table
  base := (-411757470907293919587390389798872530281/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-9979790871574302231113984255712840000000000000)
      constant := (113661711885775073094218433132760976479793403820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree056.table
  base := (-4120258146039212732998260758839102477217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-62721896085641458660764335730420000000000000)
      constant := (727746330463779836669963202984509268708689927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73818767747321509021/20000000000000000000)
  centralHi := (184546919368303772553/50000000000000000000)
  directionLo := (186217061278036887783/50000000000000000000)
  directionHi := (372434122556073775567/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree057.table
  base := (-881318530085431300853747017347666097213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1130503765327376373159840027586020000000000000)
      constant := (13149718259268018823446606106395670248129909016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree057.table
  base := (-705526428214982306945597228754724967863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-63943982197980125019021180275840000000000000)
      constant := (757656553448651193693589178825863907594977765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186217061278036887783/50000000000000000000)
  centralHi := (372434122556073775567/100000000000000000000)
  directionLo := (187872356598103799981/50000000000000000000)
  directionHi := (375744713196207599963/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree058.table
  base := (-2907267294642833283679871970680863086563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-10369276904318472485763136240835520000000000000)
      constant := (123126932345249858212972780829410919546388230986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree058.table
  base := (-581867745056477756848381841339103301439/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-65166068310318791377278024821260000000000000)
      constant := (788163414143534421916532813918273837901650045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187872356598103799981/50000000000000000000)
  centralHi := (375744713196207599963/100000000000000000000)
  directionLo := (473782985899280207/125000000000000000)
  directionHi := (379026388719424165601/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree059.table
  base := (-1131801795094787741546349903232527512177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-10564019920690557613087712233396860000000000000)
      constant := (128000104974722307581046556894901588026808818588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree059.table
  base := (-906169089018266236796211241447264081/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-66388154422657457735534869366680000000000000)
      constant := (819266851184532296438587376286156738682777500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473782985899280207/125000000000000000)
  centralHi := (379026388719424165601/100000000000000000000)
  directionLo := (382279893790499731317/100000000000000000000)
  directionHi := (191139946895249865659/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree060.table
  base := (-1594325690365145374257953433409618283219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1195418104118071415601365358439800000000000000)
      constant := (14774108083954906623455078486313920186264917402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree060.table
  base := (-1595922796095604072670641526185638803177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-67610240534996124093791713912100000000000000)
      constant := (850966811641681767024732948520651860478450687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382279893790499731317/100000000000000000000)
  centralHi := (191139946895249865659/50000000000000000000)
  directionLo := (192752970824876963617/50000000000000000000)
  directionHi := (77101188329950785447/20000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree061.table
  base := (-899470508394767735991918809039556707251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-10953505953434727867736864218519540000000000000)
      constant := (138027527501324150402123911008094020192579287722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree061.table
  base := (-225218074333827810876657922152897218637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-68832326647334790452048558457520000000000000)
      constant := (883263249856911980168389351370500734830743788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192752970824876963617/50000000000000000000)
  centralHi := (77101188329950785447/20000000000000000000)
  directionLo := (97176303984707096249/25000000000000000000)
  directionHi := (388705215938828384997/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree062.table
  base := (-179069969352500428477488227947130129169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-11148248969806812995061440211080880000000000000)
      constant := (143181762131633205550015529301397721374213157518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree062.table
  base := (-90149998830321130972041690852945461017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-70054412759673456810305403002940000000000000)
      constant := (916156126442182010159013579257084635327735454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97176303984707096249/25000000000000000000)
  centralHi := (388705215938828384997/100000000000000000000)
  directionLo := (195939186196150493899/50000000000000000000)
  directionHi := (391878372392300987799/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree063.table
  base := (113369662772783842980922880725434216433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1260332442908766458042890689293580000000000000)
      constant := (16492185613620898962716450118917575749806709930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree063.table
  base := (141442320148698533616600195904807063717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-71276498872012123168562247548360000000000000)
      constant := (949645407415717146634898857206064723480914292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195939186196150493899/50000000000000000000)
  centralHi := (391878372392300987799/100000000000000000000)
  directionLo := (197513020203496112253/50000000000000000000)
  directionHi := (395026040406992224507/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree064.table
  base := (1338260456212220182638683646364096263863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-11537735002550983249710592196203560000000000000)
      constant := (153771247377011900965029546193754056541207008414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree064.table
  base := (33432853004603461230946985531245443141/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-72498584984350789526819092093780000000000000)
      constant := (983731063457306438945354562459851000466401160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197513020203496112253/50000000000000000000)
  centralHi := (395026040406992224507/100000000000000000000)
  directionLo := (49768603062450172227/12500000000000000000)
  directionHi := (398148824499601377817/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree065.table
  base := (2135145795410389497617357844595609271089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-11732478018923068377035168188764900000000000000)
      constant := (159206488112465056177723098218614600032923576242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree065.table
  base := (426863207990447658877807429954686883023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-73720671096689455885075936639200000000000000)
      constant := (1018413069266248483471234274261289831714292435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768603062450172227/12500000000000000000)
  centralHi := (398148824499601377817/100000000000000000000)
  directionLo := (100311826415558457011/25000000000000000000)
  directionHi := (80249461132446765609/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree066.table
  base := (295748645532403081475093960690417095639/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1325246781699461500484416020147360000000000000)
      constant := (18303932084934913572211933804085112580707362380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree066.table
  base := (2956759090484709725253280349508691526973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-74942757209028122243332781184620000000000000)
      constant := (1053691403007794988592289425945037398700426037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100311826415558457011/25000000000000000000)
  centralHi := (80249461132446765609/20000000000000000000)
  directionLo := (101080510656107017063/25000000000000000000)
  directionHi := (404322042624428068253/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree067.table
  base := (380526696854996941287708683818254065691/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-12121964051667238631684320173887580000000000000)
      constant := (170357945902529657598272522343039602501808185980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree067.table
  base := (3804629505489637769835294960475155276417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-76164843321366788601589625730040000000000000)
      constant := (1089566045835892322711858432562980487573414873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101080510656107017063/25000000000000000000)
  centralHi := (404322042624428068253/100000000000000000000)
  directionLo := (203686786514723109767/50000000000000000000)
  directionHi := (81474714605889243907/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree068.table
  base := (2339236975084507472270108525429423376557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-12316707068039323759008896166448920000000000000)
      constant := (176074156558330754325940448364506653315212116692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree068.table
  base := (4677915401228925604380018329418510707707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-77386929433705454959846470275460000000000000)
      constant := (1126036981481703031278220613342813941158850883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203686786514723109767/50000000000000000000)
  centralHi := (81474714605889243907/20000000000000000000)
  directionLo := (82080482906368253649/20000000000000000000)
  directionHi := (205201207265920634123/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree069.table
  base := (278854790786464005848843913456084891489/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1390161120490156542925941351001140000000000000)
      constant := (20209335351404549074766298827652851877921438760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree069.table
  base := (5576606517375434889806333293888690024817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-78609015546044121318103314820880000000000000)
      constant := (1163104195898839261905173918889143616643974473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82080482906368253649/20000000000000000000)
  centralHi := (205201207265920634123/50000000000000000000)
  directionLo := (413409065822646179727/100000000000000000000)
  directionHi := (25838066613915386233/6250000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree070.table
  base := (6501122537462345944622114646015056659451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-12706193100783494013658048151571600000000000000)
      constant := (187787528491521795213360620818320427235819723878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree070.table
  base := (6500693993585193723751703672407607437107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-79831101658382787676360159366300000000000000)
      constant := (1200767676957490117058384037169526014581399483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (413409065822646179727/100000000000000000000)
  centralHi := (25838066613915386233/6250000000000000000)
  directionLo := (208197003793967173359/50000000000000000000)
  directionHi := (416394007587934346719/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree071.table
  base := (7450545433547874332019880115478195704043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-12900936117155579140982624144132940000000000000)
      constant := (193784685619536564005198191488402118286851248454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree071.table
  base := (7450170176861207888165255692651861397011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-81053187770721454034617003911720000000000000)
      constant := (1239027414180702711653339321989650398252508059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208197003793967173359/50000000000000000000)
  centralHi := (416394007587934346719/100000000000000000000)
  directionLo := (419357703405968746219/100000000000000000000)
  directionHi := (20967885170298437311/5000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree072.table
  base := (8425356985945295310280278589716051063797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1455075459280851585367466681854920000000000000)
      constant := (22208387542149916280205437564951302930314085674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree072.table
  base := (4212514227732073121191097470954002643161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-82275273883060120392873848457140000000000000)
      constant := (1277883398517005901358469669798512059236974818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419357703405968746219/100000000000000000000)
  centralHi := (20967885170298437311/5000000000000000000)
  directionLo := (211150300293840557703/50000000000000000000)
  directionHi := (422300600587681115407/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree073.table
  base := (2356387670729723170016224399541363837337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-13290422149899749395631776129255620000000000000)
      constant := (206059933826800119096055986165902693356467700744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree073.table
  base := (9425263115710341417688236419352474183733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-83497359995398786751130693002560000000000000)
      constant := (1317335622144366745546005224429983537157530477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211150300293840557703/50000000000000000000)
  centralHi := (422300600587681115407/100000000000000000000)
  directionLo := (425223130964795823037/100000000000000000000)
  directionHi := (212611565482397911519/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree074.table
  base := (5225560441453952059485283630041890020809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59940000000000000000000000000000000000000000
      center := (259515)
      previous := (214011)
      next := (0)
      square := (5822880888201880883459082834060000000000000)
      linear := (-364463923412752284404225733022080000000000000)
      constant := (5738865465154462675175173122232802177569458292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree074.table
  base := (326589663078189054118669928509084344677/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1580)
      previous := (1343)
      next := (0)
      square := (35943709186431363478142486630000000000000)
      linear := (-2289714759668579813767230744540000000000000)
      constant := (36686056170301633327429635965434755864097568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425223130964795823037/100000000000000000000)
  centralHi := (212611565482397911519/50000000000000000000)
  directionLo := (428125711629530170359/100000000000000000000)
  directionHi := (10703142790738254259/2500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree075.table
  base := (2300412539369462690058561529668385783851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1519989798071546627808992012708700000000000000)
      constant := (24301083549645242780054225556157316812428281710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree075.table
  base := (8985814447554585221932858327801063033/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-85941532220076119467644382093400000000000000)
      constant := (1398028761140429852589373260391222358773986560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428125711629530170359/100000000000000000000)
  centralHi := (10703142790738254259/2500000000000000000)
  directionLo := (431008745629458602079/100000000000000000000)
  directionHi := (2693804660184116263/625000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree076.table
  base := (3144592971609375563090734348778236241503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-13874651199016004777605504106939640000000000000)
      constant := (225175122095114704438755022797915278708672209336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree076.table
  base := (1257817924418220745344424588451235597669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-87163618332414785825901226638820000000000000)
      constant := (1439269665604224354492585308167657415332088610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (431008745629458602079/100000000000000000000)
  centralHi := (2693804660184116263/625000000000000000)
  directionLo := (108468155655204593059/25000000000000000000)
  directionHi := (433872622620818372237/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree077.table
  base := (13680044776200194261068414608575103116143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-14069394215388089904930080099500980000000000000)
      constant := (231734131840497456082980032584427524218891962254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree077.table
  base := (213748066796874890612370662740798285917/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-88385704444753452184158071184240000000000000)
      constant := (1481106787315249849474592090876187782618903872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108468155655204593059/25000000000000000000)
  centralHi := (433872622620818372237/100000000000000000000)
  directionLo := (43671771948325476543/10000000000000000000)
  directionHi := (436717719483254765431/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree078.table
  base := (115680298261338953253151861512529112331/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1584904136862241670250517343562480000000000000)
      constant := (26487420052863942114867765869713363025415744256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree078.table
  base := (14806930816833545850313354349324025084937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-89607790557092118542414915729660000000000000)
      constant := (1523540122483443965791990318203664590341278753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43671771948325476543/10000000000000000000)
  centralHi := (436717719483254765431/100000000000000000000)
  directionLo := (439544400898751665129/100000000000000000000)
  directionHi := (43954440089875166513/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree079.table
  base := (15959469322575449322739993345425767957437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-14458880248132260159579232084623660000000000000)
      constant := (245133067387152514501274613606293830966064462986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree079.table
  base := (15959340471298835374114270497029304966157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-90829876669430784900671760275080000000000000)
      constant := (1566569667825418965508620711492043118498668933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439544400898751665129/100000000000000000000)
  centralHi := (43954440089875166513/10000000000000000000)
  directionLo := (22117650994863256967/5000000000000000000)
  directionHi := (442353019897265139341/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree080.table
  base := (3427443161640741571992327253022622047427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-14653623264504345286903808077185000000000000000)
      constant := (251972992041614264188451410301436255362171326030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree080.table
  base := (17137103159377522062257484053048794688619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-92051962781769451258928604820500000000000000)
      constant := (1610195420494998741837569935804623799928719411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22117650994863256967/5000000000000000000)
  centralHi := (442353019897265139341/100000000000000000000)
  directionLo := (445143918371371185161/100000000000000000000)
  directionHi := (222571959185685592581/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree081.table
  base := (4585078886522548260755555652459308274011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1649818475652936712692042674416260000000000000)
      constant := (28767394886225968186053991010560164097952716248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree081.table
  base := (18340217077663797025497651303708262245951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-93274048894108117617185449365920000000000000)
      constant := (1654417378023320742409461115597386611014706919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (445143918371371185161/100000000000000000000)
  centralHi := (222571959185685592581/50000000000000000000)
  directionLo := (447917427562051550043/100000000000000000000)
  directionHi := (111979356890512887511/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree082.table
  base := (1223047920040062642345484827718757694761/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-15043109297248515541552960062307680000000000000)
      constant := (265933752787752078429798628533815950304459280928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree082.table
  base := (195686806606350217906446439244797882111/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-94496135006446783975442293911340000000000000)
      constant := (1699235538267184475154496965194052830060995900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447917427562051550043/100000000000000000000)
  centralHi := (111979356890512887511/25000000000000000000)
  directionLo := (14083558391174112781/3125000000000000000)
  directionHi := (450673868517571608993/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree083.table
  base := (260282096902439988043698203900597769599/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-15237852313620600668877536054869020000000000000)
      constant := (273054588126435315274860885491375296771690161760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree083.table
  base := (10411246274057965619976535381989038687251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-95718221118785450333699138456760000000000000)
      constant := (1744649899364510002126484044108375987925693238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14083558391174112781/3125000000000000000)
  centralHi := (450673868517571608993/100000000000000000000)
  directionLo := (453413552527249836849/100000000000000000000)
  directionHi := (9068271050544996737/2000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree084.table
  base := (690678664539922482166496096684582828189/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1714732814443631755133568005270040000000000000)
      constant := (31141006631892585681098462859850927681671466816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree084.table
  base := (1105082577861030989068179748954705318743/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-96940307231124116691955983002180000000000000)
      constant := (1790660459695926518569893120202139831627183340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453413552527249836849/100000000000000000000)
  centralHi := (9068271050544996737/2000000000000000000)
  directionLo := (18245471261271115617/4000000000000000000)
  directionHi := (228068390765888945213/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree085.table
  base := (11703107030574443132167080210677616117123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-15627338346364770923526688039991700000000000000)
      constant := (287577167203691990938113259375434195694446609388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree085.table
  base := (5851539164538802101797459644013343576551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-98162393343462783050212827547600000000000000)
      constant := (1837267217851646204123201542001867069425193276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18245471261271115617/4000000000000000000)
  centralHi := (228068390765888945213/50000000000000000000)
  directionLo := (114710962127905575617/25000000000000000000)
  directionHi := (458843848511622302469/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree086.table
  base := (309200713675901617564376665118847157039/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-15822081362736856050851264032553040000000000000)
      constant := (294978910444489976579487056781415034783503627360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree086.table
  base := (24736006953349163580478708124351170257617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-99384479455801449408469672093020000000000000)
      constant := (1884470172602894998374320524601196752082677673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114710962127905575617/25000000000000000000)
  centralHi := (458843848511622302469/100000000000000000000)
  directionLo := (115383759463730510119/25000000000000000000)
  directionHi := (461535037854922040477/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree087.table
  base := (26091245450789313524513369427336195453037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1779647153234326797575093336123820000000000000)
      constant := (33608254356320745519221994675538613528353737754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree087.table
  base := (652280041486414584780079255440042189671/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-100606565568140115766726516638440000000000000)
      constant := (1932269322877272361608423059266786710306383960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115383759463730510119/25000000000000000000)
  centralHi := (461535037854922040477/100000000000000000000)
  directionLo := (232105312853094794017/50000000000000000000)
  directionHi := (92842125141237917607/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree088.table
  base := (5494355666555072751516158756554915951541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-16211567395481026305500416017675720000000000000)
      constant := (310063303313786896165270777718607860749504299490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree088.table
  base := (3433967511478999888956523133208688498519/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-101828651680478782124983361183860000000000000)
      constant := (1980664667737498647137272732525941556435780088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232105312853094794017/50000000000000000000)
  centralHi := (92842125141237917607/20000000000000000000)
  directionLo := (233435440148512887617/50000000000000000000)
  directionHi := (93374176059405155047/20000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree089.table
  base := (5775531008178341536718770943437142050039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-16406310411853111432824992010237060000000000000)
      constant := (317745952610136981741974543650124607447867746710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree089.table
  base := (1443881082556987760405317844606317984249/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-103050737792817448483240205729280000000000000)
      constant := (2029656206363083342535207691560730986408737620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233435440148512887617/50000000000000000000)
  centralHi := (93374176059405155047/20000000000000000000)
  directionLo := (469516062259969435097/100000000000000000000)
  directionHi := (234758031129984717549/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree090.table
  base := (7577218740528668810505100489463362802247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1844561492025021840016618666977600000000000000)
      constant := (36169137439997978100491616739023924744691882296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree090.table
  base := (15154422905901514955290089121751744943189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-104272823905156114841497050274700000000000000)
      constant := (2079243938034511778799117776667356277654451482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469516062259969435097/100000000000000000000)
  centralHi := (234758031129984717549/50000000000000000000)
  directionLo := (29509151557907581619/6250000000000000000)
  directionHi := (94429284985304261181/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree091.table
  base := (6353087511611500376103138254724194570641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-16795796444597281687474143995359740000000000000)
      constant := (333392156243919019783730886035782507117438098490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree091.table
  base := (6353082422407815558436949786840946493989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-105494910017494781199753894820120000000000000)
      constant := (2129427862119603377439592083491736278751354705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29509151557907581619/6250000000000000000)
  centralHi := (94429284985304261181/20000000000000000000)
  directionLo := (237381107305153364539/50000000000000000000)
  directionHi := (474762214610306729079/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree092.table
  base := (16623671177521451436828506453726089463071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-16990539460969366814798719987921080000000000000)
      constant := (341355710356897431528058752079330209337881920476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree092.table
  base := (33247320145262208804297259665845653006289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-106716996129833447558010739365540000000000000)
      constant := (2180207978061742328780065986104382698965609641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237381107305153364539/50000000000000000000)
  centralHi := (474762214610306729079/100000000000000000000)
  directionLo := (477363670876272976637/100000000000000000000)
  directionHi := (238681835438136488319/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree093.table
  base := (34754588935516139453101162075538467590869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1909475830815716882458143997831380000000000000)
      constant := (38823655467368064809204725501257213918374193898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree093.table
  base := (2172160597041633439783245592861469890161/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-107939082242172113916267583910960000000000000)
      constant := (2231584285369722824671221350381127636474086544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477363670876272976637/100000000000000000000)
  centralHi := (238681835438136488319/50000000000000000000)
  directionLo := (239975513398376956951/50000000000000000000)
  directionHi := (479951026796753913903/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree094.table
  base := (9071794232654245318331862507556360630349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-17380025493713537069447871973043760000000000000)
      constant := (357563722710359390882513331022659358191510162088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree094.table
  base := (2267947501051455070343455948520410449251/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-109161168354510780274524428456380000000000000)
      constant := (2283556783608986514440572525176951070480393904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239975513398376956951/50000000000000000000)
  centralHi := (479951026796753913903/100000000000000000000)
  directionLo := (15078890912349270401/3125000000000000000)
  directionHi := (482524509195176652833/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree095.table
  base := (37845106013753590844977887078835676014217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-17574768510085622196772447965605100000000000000)
      constant := (365808180796606969792356320375300893555081017826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree095.table
  base := (37845091256161039185608990714481251249931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-110383254466849446632781273001800000000000000)
      constant := (2336125472394060497892762727406374832961155539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15078890912349270401/3125000000000000000)
  centralHi := (482524509195176652833/100000000000000000000)
  directionLo := (97016867775626284203/20000000000000000000)
  directionHi := (60635542359766427627/12500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree096.table
  base := (19714187947521318878078813975228283467109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-1974390169606411924899669328685160000000000000)
      constant := (41571808155640619417809142508305230722392999956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree096.table
  base := (2464272688762140494907428460352617196819/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-111605340579188112991038117547220000000000000)
      constant := (2389290351382030589210345111023723727079123376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97016867775626284203/20000000000000000000)
  centralHi := (60635542359766427627/12500000000000000000)
  directionLo := (48763073085647664861/10000000000000000000)
  directionHi := (487630730856476648611/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree097.table
  base := (41036986316498346585600019569737411251329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-17964254542829792451421599950727780000000000000)
      constant := (382578000465619636484913541835252778592497242962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree097.table
  base := (8207395017081962734386435986611013470323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-112827426691526779349294962092640000000000000)
      constant := (2443051420266907363183330957138642387204360935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48763073085647664861/10000000000000000000)
  centralHi := (487630730856476648611/100000000000000000000)
  directionLo := (122540973639026472201/25000000000000000000)
  directionHi := (98032778911221177761/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree098.table
  base := (21335468523934541898589074519367098644527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-18158997559201877578746175943289120000000000000)
      constant := (391103361940104408183874943668137772806371818012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree098.table
  base := (8534185450342747099807171147297136042991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-114049512803865445707551806638060000000000000)
      constant := (2497408678774762132515533119967888896214273395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122540973639026472201/25000000000000000000)
  centralHi := (98032778911221177761/20000000000000000000)
  directionLo := (492684034018961301307/100000000000000000000)
  directionHi := (123171008504740325327/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree099.table
  base := (44330227883033833919169125456733338072713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-2039304508397106967341194659538940000000000000)
      constant := (44413595308722975920875414308358177916787793746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree099.table
  base := (11082554834840790743931384039828133732627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-115271598916204112065808651183480000000000000)
      constant := (2552362126659526934976352748993308860319865452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492684034018961301307/100000000000000000000)
  centralHi := (123171008504740325327/25000000000000000000)
  directionLo := (495191348094839740101/100000000000000000000)
  directionHi := (247595674047419870051/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree100.table
  base := (9202971727376559279571288671450774148221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-18548483591946047833395327928411800000000000000)
      constant := (408434987939773480449722758007165048945220784690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree100.table
  base := (46014851186316777321691299903462023112621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-116493685028542778424065495728900000000000000)
      constant := (2607911763699367205155545561957839509641178149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495191348094839740101/100000000000000000000)
  centralHi := (247595674047419870051/50000000000000000000)
  directionLo := (49768603062450172227/10000000000000000000)
  directionHi := (497686030624501722271/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree101.table
  base := (5965603642827075557144880641130169562421/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-18743226608318132960719903920973140000000000000)
      constant := (417241252386912069704541326569053328961716836304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree101.table
  base := (11931205661486494577097529334848704856967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-117715771140881444782322340274320000000000000)
      constant := (2664057589693548389340236151298641507796751292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768603062450172227/10000000000000000000)
  centralHi := (497686030624501722271/100000000000000000000)
  directionLo := (62521033826820058283/12500000000000000000)
  directionHi := (100033654122912093253/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree102.table
  base := (24730069624703772297842681261358515934899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-2104218847187802009782719990392720000000000000)
      constant := (47349016787385809156380312804186413099335562316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree102.table
  base := (49460133585057284178396281879607522519747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-118937857253220111140579184819740000000000000)
      constant := (2720799604459728611004508724697422698329533643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62521033826820058283/12500000000000000000)
  centralHi := (100033654122912093253/20000000000000000000)
  directionLo := (125659563101149387681/25000000000000000000)
  directionHi := (20105530096183902029/4000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree103.table
  base := (6402598602546728609842669561883606790183/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-19132712641062303215369055906095820000000000000)
      constant := (435134684008096749393786649422112735373705642992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree103.table
  base := (25610391941091592030953943689324203641227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-120159943365558777498836029365160000000000000)
      constant := (2778137807831618847767604472641059669569679526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125659563101149387681/25000000000000000000)
  centralHi := (20105530096183902029/4000000000000000000)
  directionLo := (505096155826923355277/100000000000000000000)
  directionHi := (252548077913461677639/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree104.table
  base := (53006777730824605189922752705832186992823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-19327455657434388342693631898657160000000000000)
      constant := (444221851124131782862960921967723170766894299294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree104.table
  base := (530067734261045727838194006446898643683/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-121382029477897443857092873910580000000000000)
      constant := (2836072199656960144644803920189940424320202700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (505096155826923355277/100000000000000000000)
  centralHi := (252548077913461677639/50000000000000000000)
  directionLo := (253771078179687058683/50000000000000000000)
  directionHi := (507542156359374117367/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree105.table
  base := (5481810586673912420886720537081541055951/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-2169133185978497052224245321246500000000000000)
      constant := (50378072489921121008019368061242508347007445420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree105.table
  base := (27409051057286488183723691763477175442081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-122604115590236110215349718456000000000000000)
      constant := (2894602779795774340762027440515650506360417778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253771078179687058683/50000000000000000000)
  centralHi := (507542156359374117367/100000000000000000000)
  directionLo := (50997642527151300611/10000000000000000000)
  directionHi := (509976425271513006111/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree106.table
  base := (708184664043105475680749771895686739673/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-19716941690178558597342783883779840000000000000)
      constant := (462677087840358398098248957975242149100095887520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree106.table
  base := (56654769853205154912960868713991565007051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-123826201702574776573606563001420000000000000)
      constant := (2953729548118850780696406439368814452494652819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50997642527151300611/10000000000000000000)
  centralHi := (509976425271513006111/100000000000000000000)
  directionLo := (8006236402571561287/1562500000000000000)
  directionHi := (512399129764579922369/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree107.table
  base := (29258389702246144854793881725420683947773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-19911684706550643724667359876341180000000000000)
      constant := (472045157395943947060443500712339051889138400788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree107.table
  base := (11703355310905288875602953822727718114271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-125048287814913442931863407546840000000000000)
      constant := (3013452504506436649373970492520261230492184995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8006236402571561287/1562500000000000000)
  centralHi := (512399129764579922369/100000000000000000000)
  directionLo := (257405216552756822131/50000000000000000000)
  directionHi := (514810433105513644263/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree108.table
  base := (60404124620627555658618507744424187117751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-2234047524769192094665770652100280000000000000)
      constant := (53500762339583841612412010843471220818955620142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree108.table
  base := (30202061068571226662699260101406947173869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-126270373927252109290120252092260000000000000)
      constant := (3073771648847103024917178337137892221362053322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257405216552756822131/50000000000000000000)
  centralHi := (514810433105513644263/100000000000000000000)
  directionLo := (103442098951070064499/20000000000000000000)
  directionHi := (8081413980552348789/1562500000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree109.table
  base := (31158404344483902698253340122737304747221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-20301170739294813979316511861463860000000000000)
      constant := (491062198802907893667494760086683662944458357876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree109.table
  base := (31158403262510768332551573171730343021889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-127492460039590775648377096637680000000000000)
      constant := (3134686981036762585197807685573207679193932082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103442098951070064499/20000000000000000000)
  centralHi := (8081413980552348789/1562500000000000000)
  directionLo := (64949933811535509249/12500000000000000000)
  directionHi := (519599470492284073993/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree110.table
  base := (64254831532236308699452504275602068737867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-20495913755666899106641087854025200000000000000)
      constant := (500711170618765625852229621326486975600546667526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree110.table
  base := (64254829646872887652267789127174637277/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-128714546151929442006633941183100000000000000)
      constant := (3196198500977818215782144022665102078432213000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64949933811535509249/12500000000000000000)
  centralHi := (519599470492284073993/100000000000000000000)
  directionLo := (104395502505931683987/20000000000000000000)
  directionHi := (16311797266551825623/3125000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree111.table
  base := (1324363861562344272747188912621025109721/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6660000000000000000000000000000000000000000
      center := (28835)
      previous := (23779)
      next := (0)
      square := (646986765355764542606564759340000000000000)
      linear := (-62134104420537490192089080620380000000000000)
      constant := (1532894223687056174344023219663695136153709300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree111.table
  base := (33109095717803587613394163919541288301837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (1580)
      previous := (1343)
      next := (0)
      square := (35943709186431363478142486630000000000000)
      linear := (-3511800872007246172024075289960000000000000)
      constant := (88062329961579043849970400193376055334335938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104395502505931683987/20000000000000000000)
  centralHi := (16311797266551825623/3125000000000000000)
  directionLo := (262172384814570734299/50000000000000000000)
  directionHi := (524344769629141468599/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree112.table
  base := (6820689325869168613166299594658617491461/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-20885399788411069361290239839147880000000000000)
      constant := (520290016394917231096209213015028868700212376580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree112.table
  base := (8525861478483556520263812137264052866219/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-131158718376606774723147630273940000000000000)
      constant := (3321010103751847513444937249735955906990830488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262172384814570734299/50000000000000000000)
  centralHi := (524344769629141468599/100000000000000000000)
  directionLo := (65837673401165370751/12500000000000000000)
  directionHi := (526701387209322966009/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree113.table
  base := (70220932009947589392393568706481489358419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-21080142804783154488614815831709220000000000000)
      constant := (530219890325951717298172188969257606746931448982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree113.table
  base := (70220930763627610058931889435181754134609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-132380804488945441081404474819360000000000000)
      constant := (3384310186415907039371596354583053821410279721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65837673401165370751/12500000000000000000)
  centralHi := (526701387209322966009/100000000000000000000)
  directionLo := (264523753724978773767/50000000000000000000)
  directionHi := (105809501489991509507/20000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree114.table
  base := (18065077317838206703916752258434894654363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-2363876202350582179548821313807840000000000000)
      constant := (60027044251940941926870271101153990696291252184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree114.table
  base := (18065077046457248534792859845517881396841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-133602890601284107439661319364780000000000000)
      constant := (3448206456492494008837689143070215918529101316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264523753724978773767/50000000000000000000)
  centralHi := (105809501489991509507/20000000000000000000)
  directionLo := (531383269392065646941/100000000000000000000)
  directionHi := (265691634696032823471/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree115.table
  base := (1858125624637095193553567676159933837231/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-21469628837527324743263967816831900000000000000)
      constant := (550360540206732222137942724060011787262136668720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree115.table
  base := (74325024040082943520835735057896037195763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-134824976713622773797918163910200000000000000)
      constant := (3512698913907148976095766634332509674920999547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531383269392065646941/100000000000000000000)
  centralHi := (265691634696032823471/50000000000000000000)
  directionLo := (533708809034091488157/100000000000000000000)
  directionHi := (266854404517045744079/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree116.table
  base := (76415079097701650267346237077744023274113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-21664371853899409870588543809393240000000000000)
      constant := (560571316131625249735492512242623433993686232914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree116.table
  base := (19103769568599504144562528246088293044417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-136047062825961440156175008455620000000000000)
      constant := (3577787558588695657560280214068139492711227492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533708809034091488157/100000000000000000000)
  centralHi := (266854404517045744079/50000000000000000000)
  directionLo := (536024259424306336819/100000000000000000000)
  directionHi := (26801212971215316841/5000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree117.table
  base := (15706094311173946720729339055893433007981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-2428790541141277221990346644661620000000000000)
      constant := (63430636225620533849938066429394424880913339010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree117.table
  base := (15706094167789503601266588417701720632617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-137269148938300106514431853001040000000000000)
      constant := (3643472390468921307358573129338258277730263365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536024259424306336819/100000000000000000000)
  centralHi := (26801212971215316841/5000000000000000000)
  directionLo := (269164875374817333077/50000000000000000000)
  directionHi := (107665950149926933231/20000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree118.table
  base := (80671202310107075539292269614573269888813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-22053857886643580125237695794515920000000000000)
      constant := (581273769892548382406835087555850610649401169514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree118.table
  base := (3226848067434627327414614305799133451243/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-138491235050638772872688697546460000000000000)
      constant := (3709753409482297693726250254333815342368791675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269164875374817333077/50000000000000000000)
  centralHi := (107665950149926933231/20000000000000000000)
  directionLo := (33789088151316940151/6250000000000000000)
  directionHi := (540625410421071042417/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree119.table
  base := (82837271312572756662860418736359497819463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-22248600903015665252562271787077260000000000000)
      constant := (591765447706905919582443512941736731707404865214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree119.table
  base := (2588664711533422270471072505507793262377/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-139713321162977439230945542091880000000000000)
      constant := (3776630615565737190402197798010095407238211616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33789088151316940151/6250000000000000000)
  centralHi := (540625410421071042417/100000000000000000000)
  directionLo := (542911363155846310501/100000000000000000000)
  directionHi := (271455681577923155251/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree120.table
  base := (85028678517277258074944934901730292257211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-2493704879931972264431871975515400000000000000)
      constant := (66927862162606439183755040453484437861802193462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree120.table
  base := (850286780441027989813120270849325775737/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-140935407275316105589202386637300000000000000)
      constant := (3844104008658379249409067418611272698698395300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542911363155846310501/100000000000000000000)
  centralHi := (271455681577923155251/50000000000000000000)
  directionLo := (54518773105649301597/10000000000000000000)
  directionHi := (545187731056493015971/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree121.table
  base := (17449084775983427399210418711791281086527/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-22638086935759835507211423772199940000000000000)
      constant := (613029705152378952688140081731086828684038925030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree121.table
  base := (87245423467999362128593145039103937865627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-142157493387654771947459231182720000000000000)
      constant := (3912173588701403170278279694805943290938043363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54518773105649301597/10000000000000000000)
  centralHi := (545187731056493015971/100000000000000000000)
  directionLo := (547454633686951894497/100000000000000000000)
  directionHi := (273727316843475947249/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree122.table
  base := (3579500294309197873810334050774061179959/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-22832829952131920634535999764761280000000000000)
      constant := (623802284764185149807653604274172423509223677550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree122.table
  base := (44743753499581459031612897999965394465057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-143379579499993438305716075728140000000000000)
      constant := (3980839355637863640167710445558945250045326066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547454633686951894497/100000000000000000000)
  centralHi := (273727316843475947249/50000000000000000000)
  directionLo := (274856094072926827981/50000000000000000000)
  directionHi := (549712188145853655963/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree123.table
  base := (91754928909366725246595281061150233771501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-2558619218722667306873397306369180000000000000)
      constant := (70518722032189583759390933990408059060597327642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree123.table
  base := (45877464298630678846618889116048518276579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-144601665612332104663972920273560000000000000)
      constant := (4050101309412546001730449726694630843041273302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274856094072926827981/50000000000000000000)
  centralHi := (549712188145853655963/100000000000000000000)
  directionLo := (110392101827420630623/20000000000000000000)
  directionHi := (137990127284275788279/25000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree124.table
  base := (94047688494779733869250608527088928554939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-23222315984876090889185151749883960000000000000)
      constant := (645628345720060557457203602056093048397057261542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree124.table
  base := (94047688223133517151927364040957996241329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-145823751724670771022229764818980000000000000)
      constant := (4119959449971838621632982872999031496854379401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110392101827420630623/20000000000000000000)
  centralHi := (137990127284275788279/25000000000000000000)
  directionLo := (554199709037886321803/100000000000000000000)
  directionHi := (138549927259471580451/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree125.table
  base := (96365786075123445673242363626701801162451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-23417059001248176016509727742445300000000000000)
      constant := (656681827046632977379836071349799547058206057878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree125.table
  base := (96365785838706782532453325066512038606301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-147045837837009437380486609364400000000000000)
      constant := (4190413777263620091436844242847304980852026069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554199709037886321803/100000000000000000000)
  centralHi := (138549927259471580451/25000000000000000000)
  directionLo := (556429897964213981451/100000000000000000000)
  directionHi := (139107474491053495363/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree126.table
  base := (98709221612667044626560689305388334269371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-2623533557513362349314922637222960000000000000)
      constant := (74203215806783960964940970190770759333065840182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree126.table
  base := (49354610703462049120557488730748457867437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-148267923949348103738743453909820000000000000)
      constant := (4261464291237159302034257600052549277641042506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556429897964213981451/100000000000000000000)
  centralHi := (139107474491053495363/25000000000000000000)
  directionLo := (558651183834110663349/100000000000000000000)
  directionHi := (11173023676682213267/2000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree127.table
  base := (101077995070716935998510586101942997281987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-23806545033992346271158879727567980000000000000)
      constant := (679069691355190739318917507566997669051204512886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree127.table
  base := (50538997445839571561238246325818728618453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-149490010061686770097000298455240000000000000)
      constant := (4333110991843026699763431295296581678957324314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558651183834110663349/100000000000000000000)
  centralHi := (11173023676682213267/2000000000000000000)
  directionLo := (70107959053568883117/12500000000000000000)
  directionHi := (560863672428551064937/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree128.table
  base := (51736053206773983428846204279215624247159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2217780000000000000000000000000000000000000000
      center := (9602055)
      previous := (7918407)
      next := (0)
      square := (215446592863469592687986064860220000000000000)
      linear := (-24001288050364431398483455720129320000000000000)
      constant := (690404074321115196316362448329612245428572857404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree128.table
  base := (10347210625775860670130151585805453650397/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-150712096174025436455257143000660000000000000)
      constant := (4405353879033015262583766758887116660473934930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell027.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70107959053568883117/12500000000000000000)
  centralHi := (560863672428551064937/100000000000000000000)
  directionLo := (70383433431280185901/12500000000000000000)
  directionHi := (563067467450241487209/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree129.table
  base := (105891555606342230682337852219298527327423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 246420000000000000000000000000000000000000000
      center := (1066895)
      previous := (879823)
      next := (0)
      square := (23938510318163288076442896095580000000000000)
      linear := (-2688447896304057391756447968076740000000000000)
      constant := (77981343461234130444913202553248509310402357566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree129.table
  base := (52945777735395321487620581054883752776081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (58460)
      previous := (49691)
      next := (0)
      square := (1329917239897960448691272005310000000000000)
      linear := (-151934182286364102813513987546080000000000000)
      constant := (4478192952760069933318048367298881715100909778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell027.Kernel129
