import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell186.Parameters
import ForestUnimodality.BinomialMassData.Q53_78.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_78.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_78.Batch100_149
import ForestUnimodality.BinomialMassData.Q107_156.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_156.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_156.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree000.table
  base := (107361267807396284856658043/20000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (24046046168179277535692506380000000000000)
      linear := (-38872309345411174830164924580000000000000)
      constant := (4187089444488455109409663677000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree000.table
  base := (107361267807396284856658043/20000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (1819)
      previous := (0)
      next := (833)
      square := (48092092336358555071385012760000000000000)
      linear := (-77744618690822349660329849160000000000000)
      constant := (8374178888976910218819327354000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree001.table
  base := (9785725552391629236866184365452538420447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-930153503794845842589378298920000000000000)
      constant := (40178602563834519525211427650880495833333032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree001.table
  base := (9752060667809368416846423729555102523011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-1868322356312418111023987433300000000000000)
      constant := (80096066319078451168795001715768491666665232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (29549181354690267907/100000000000000000000)
  directionHi := (7387295338672566977/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree002.table
  base := (177004064613983083687634113313054117357/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-1354966986099346412386612578300000000000000)
      constant := (29981194204539970104077580334749899999999680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree002.table
  base := (14060856396395847153626113785939299802761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-2725964669644145676463686827520000000000000)
      constant := (59593788571030642438178884892219799999998616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29549181354690267907/100000000000000000000)
  centralHi := (7387295338672566977/25000000000000000000)
  directionLo := (41788853028825162443/100000000000000000000)
  directionHi := (10447213257206290611/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree003.table
  base := (20238863565745420910685072338445592263861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-1779780468403846982183846857680000000000000)
      constant := (22851272770365706601775577129888830555555054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree003.table
  base := (2001817178202776932788016833551986758037/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-3583606982975873241903386221740000000000000)
      constant := (45323666910273011632144646248931791452990360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41788853028825162443/100000000000000000000)
  centralHi := (10447213257206290611/25000000000000000000)
  directionLo := (25590341714195245039/50000000000000000000)
  directionHi := (51180683428390490079/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree004.table
  base := (14180580520023754698831176622509552768203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-2204593950708347551981081137060000000000000)
      constant := (18061839430035644180332272923424686506957842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree004.table
  base := (2792535670836603099474102723541010035889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-4441249296307600807343085615960000000000000)
      constant := (35795240411306837156401106502465841763914460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25590341714195245039/50000000000000000000)
  centralHi := (51180683428390490079/100000000000000000000)
  directionLo := (29549181354690267907/50000000000000000000)
  directionHi := (11819672541876107163/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree005.table
  base := (4809900733837853019729024082210814817609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-2629407433012848121778315416440000000000000)
      constant := (15079530453885641882735920778048532450111052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree005.table
  base := (9417826814388225951775397281880552324307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-5298891609639328372782785010180000000000000)
      constant := (29918650324937367490861993127891260113694596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29549181354690267907/50000000000000000000)
  centralHi := (11819672541876107163/20000000000000000000)
  directionLo := (66073978188556763199/100000000000000000000)
  directionHi := (41296236367847977/62500000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree006.table
  base := (6185518637837772505393091733709723316433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-3054220915317348691575549695820000000000000)
      constant := (13528143962260108247833509130061659442863062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree006.table
  base := (1201107895699025947192248344520000034829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-6156533922971055938222484404400000000000000)
      constant := (26927155107711909138516410741362800353166060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66073978188556763199/100000000000000000000)
  centralHi := (41296236367847977/62500000000000000)
  directionLo := (36190208317976873241/50000000000000000000)
  directionHi := (72380416635953746483/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree007.table
  base := (223427865206730911645409155661428833931/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-3479034397621849261372783975200000000000000)
      constant := (13100553361335952132170940487916021401696544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree007.table
  base := (3418688749029767040568145809108720838077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-7014176236302783503662183798620000000000000)
      constant := (26197899991953271605982479849709985859620156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36190208317976873241/50000000000000000000)
  centralHi := (72380416635953746483/100000000000000000000)
  directionLo := (39089892655028565693/50000000000000000000)
  directionHi := (78179785310057131387/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree008.table
  base := (1576682359904377176821219228408547439049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-3903847879926349831170018254580000000000000)
      constant := (13582702516793543098834900940086267103195686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree008.table
  base := (144375198873058415388719890124442607449/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-7871818549634511069101883192840000000000000)
      constant := (27297861069295023965914529674683696079065720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39089892655028565693/50000000000000000000)
  centralHi := (78179785310057131387/100000000000000000000)
  directionLo := (41788853028825162443/50000000000000000000)
  directionHi := (83577706057650324887/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree009.table
  base := (8750480400643280851467204088688069379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-4328661362230850400967252533960000000000000)
      constant := (14816380794883280534205551979908718809401224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree009.table
  base := (-19142407771045595768485231924336649667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-8729460862966238634541582587060000000000000)
      constant := (29908036315170549923476090788927281097901296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41788853028825162443/50000000000000000000)
  centralHi := (83577706057650324887/100000000000000000000)
  directionLo := (88647544064070803721/100000000000000000000)
  directionHi := (44323772032035401861/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree010.table
  base := (-1165612330420708713521274487881220049823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-4753474844535350970764486813340000000000000)
      constant := (16684555500758651422726699088688442869479478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree010.table
  base := (-1258257127960703661920805755628107312783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-9587103176297966199981281981280000000000000)
      constant := (33793216225996214504891144138436198369676076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88647544064070803721/100000000000000000000)
  centralHi := (44323772032035401861/50000000000000000000)
  directionLo := (93442716074201041839/100000000000000000000)
  directionHi := (1168033950927513023/1250000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree011.table
  base := (-2110627025479669799252654694862854726747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-5178288326839851540561721092720000000000000)
      constant := (19100563472295055478591804039714065307078542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree011.table
  base := (-6834124012785885262886270486973568713/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-10444745489629693765420981375500000000000000)
      constant := (38779785380285620406378101869391132848011520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93442716074201041839/100000000000000000000)
  centralHi := (1168033950927513023/1250000000000000000)
  directionLo := (98003547415673299907/100000000000000000000)
  directionHi := (24500886853918324977/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree012.table
  base := (-2863404964294708670939285335300899386187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-5603101809144352110358955372100000000000000)
      constant := (22000154829562008585129739112844888022406382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree012.table
  base := (-365728108287075133347198290139382681543/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-11302387802961421330860680769720000000000000)
      constant := (44739437152527645758867811192378655374646368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98003547415673299907/100000000000000000000)
  centralHi := (24500886853918324977/25000000000000000000)
  directionLo := (102361366856780980157/100000000000000000000)
  directionHi := (51180683428390490079/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree013.table
  base := (-433872680746861400323117085614350340513/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (24046046168179277535692506380000000000000)
      linear := (-463685791649911744627399203960000000000000)
      constant := (1948895059943301380469283172961645387519888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree013.table
  base := (-88044763169433415327099127417924369227/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (1819)
      previous := (0)
      next := (833)
      square := (48092092336358555071385012760000000000000)
      linear := (-935386932022549915100029243380000000000000)
      constant := (3967478841419853502082169065819651936023520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102361366856780980157/100000000000000000000)
  centralHi := (51180683428390490079/50000000000000000000)
  directionLo := (106541088522320226451/100000000000000000000)
  directionHi := (26635272130580056613/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree014.table
  base := (-1984159421854430463070529033195677124161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-6452728773753353249953423930860000000000000)
      constant := (29071554474984499020105860833479166792201492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree014.table
  base := (-3207608132279513994511741829928776089/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-13017672429624876461740079558160000000000000)
      constant := (59222790320450724898822678886340552614385000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106541088522320226451/100000000000000000000)
  centralHi := (26635272130580056613/25000000000000000000)
  directionLo := (110562912688899661017/100000000000000000000)
  directionHi := (55281456344449830509/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree015.table
  base := (-876288521653423684002383248162725082769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-6877542256057853819750658210240000000000000)
      constant := (33181521109645464220643351372039983830361170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree015.table
  base := (-275920667608416757005614132159888171091/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-13875314742956604027179778952380000000000000)
      constant := (67623918585869521880496984951513448624439232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110562912688899661017/100000000000000000000)
  centralHi := (55281456344449830509/50000000000000000000)
  directionLo := (28610871820194531437/25000000000000000000)
  directionHi := (114443487280778125749/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree016.table
  base := (-4729754769322253926715801908510754107161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-7302355738362354389547892489620000000000000)
      constant := (37645862025157807041799606094050095335338746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree016.table
  base := (-1189147272084393051602459915038585223727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-14732957056288331592619478346600000000000000)
      constant := (76741799873558345554518947900886996665126576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28610871820194531437/25000000000000000000)
  centralHi := (114443487280778125749/100000000000000000000)
  directionLo := (29549181354690267907/25000000000000000000)
  directionHi := (118196725418761071629/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree017.table
  base := (-5027742292038485362893101902090588946917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-7727169220666854959345126769000000000000000)
      constant := (42449887438845010516101272751245142807826162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree017.table
  base := (-201973299333228627233533533271682682717/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-15590599369620059158059177740820000000000000)
      constant := (86547541068423141006078645547863187986248100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29549181354690267907/25000000000000000000)
  centralHi := (118196725418761071629/100000000000000000000)
  directionLo := (121834395875919927343/100000000000000000000)
  directionHi := (7614649742244995459/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree018.table
  base := (-5286239890422854799856214810151796129531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-8151982702971355529142361048380000000000000)
      constant := (47582610950703933983237579174786078724655566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree018.table
  base := (-1325896357190957094622151958705549153607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-16448241682951786723498877135040000000000000)
      constant := (97019595558627056113342334481990585265940016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121834395875919927343/100000000000000000000)
  centralHi := (7614649742244995459/6250000000000000000)
  directionLo := (125366559086475487329/100000000000000000000)
  directionHi := (12536655908647548733/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree019.table
  base := (-2756682269872128870215761119496655415487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-8576796185275856098939595327760000000000000)
      constant := (53035801947811917403342574415885782817392364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree019.table
  base := (-5527284911418780232985957336399799332123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-17305883996283514288938576529260000000000000)
      constant := (108141867134976458650917887712278706954454556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125366559086475487329/100000000000000000000)
  centralHi := (12536655908647548733/10000000000000000000)
  directionLo := (128801895389451177721/100000000000000000000)
  directionHi := (64400947694725588861/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree020.table
  base := (-357200491411953615209390240098740444339/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-9001609667580356668736829607140000000000000)
      constant := (58803283524864157226462801746438035031044064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree020.table
  base := (-5726370926742018190418387195477465087069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-18163526309615241854378275923480000000000000)
      constant := (119902309486705954212138840510771700803424068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128801895389451177721/100000000000000000000)
  centralHi := (64400947694725588861/50000000000000000000)
  directionLo := (66073978188556763199/50000000000000000000)
  directionHi := (132147956377113526399/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree021.table
  base := (-5896349770512387496809483814812199639827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-9426423149884857238534063886520000000000000)
      constant := (64880411651550441610966397510785429565215422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree021.table
  base := (-295264861407063480080722862698032603983/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-19021168622946969419817975317700000000000000)
      constant := (132291890401904671729524873518085297582449520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66073978188556763199/50000000000000000000)
  centralHi := (132147956377113526399/100000000000000000000)
  directionLo := (13541136028184590431/10000000000000000000)
  directionHi := (135411360281845904311/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree022.table
  base := (-6060240014224859701424678225505636107823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-9851236632189357808331298165900000000000000)
      constant := (71263688280643516574229309537177284986667478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree022.table
  base := (-6067409594744481897526855502940381862561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-19878810936278696985257674711920000000000000)
      constant := (145303824640501133813103935488286905582726292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13541136028184590431/10000000000000000000)
  centralHi := (135411360281845904311/100000000000000000000)
  directionLo := (34649486478979967599/25000000000000000000)
  directionHi := (138597945915919870397/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree023.table
  base := (-248379280410639894302198831370384961431/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-10276050114493858378128532445280000000000000)
      constant := (77950473547774536695287366103065741227724150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree023.table
  base := (-1553806597341878406199907850913135391399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-20736453249610424550697374106140000000000000)
      constant := (158933004962704779330281894113990145704971312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34649486478979967599/25000000000000000000)
  centralHi := (138597945915919870397/100000000000000000000)
  directionLo := (70856447714454018589/50000000000000000000)
  directionHi := (141712895428908037179/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree024.table
  base := (-6346044284596973113909558717864945772513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-10700863596798358947925766724660000000000000)
      constant := (84938771367618872908349441220484944986671818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree024.table
  base := (-3175323481842262813462928425228855350381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-21594095562942152116137073500360000000000000)
      constant := (173175579483320410090454799593431762698854664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70856447714454018589/50000000000000000000)
  centralHi := (141712895428908037179/100000000000000000000)
  directionLo := (36190208317976873241/25000000000000000000)
  directionHi := (28952166654381498593/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree025.table
  base := (-3235709117770591069178413122542575415339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-11125677079102859517723001004040000000000000)
      constant := (92227069462276602513196993291608657057692508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree025.table
  base := (-3237553356835093648828103948012150721797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-22451737876273879681576772894580000000000000)
      constant := (188028637219311396563096280891800216672391368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36190208317976873241/25000000000000000000)
  centralHi := (28952166654381498593/20000000000000000000)
  directionLo := (29549181354690267907/20000000000000000000)
  directionHi := (9234119173340708721/6250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree026.table
  base := (-131734720669448610548928103478745134973/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (24046046168179277535692506380000000000000)
      linear := (-888499273954412314424633483340000000000000)
      constant := (7678016908537591240609899666392893973605300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree026.table
  base := (-3294846317085502726576212525277251773477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (1819)
      previous := (0)
      next := (833)
      square := (48092092336358555071385012760000000000000)
      linear := (-1793029245354277480539728637600000000000000)
      constant := (15653074903471463301925409865723497446675176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29549181354690267907/20000000000000000000)
  centralHi := (9234119173340708721/6250000000000000000)
  directionLo := (4708495385570554893/3125000000000000000)
  directionHi := (150671852338257756577/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree027.table
  base := (-6692858876867405720636359934866854850699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-11975304043711860657317469562800000000000000)
      constant := (107699349158499762688934071002510009181391214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree027.table
  base := (-6695229584259435196785255758010333146107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-24167022502937334812456171683020000000000000)
      constant := (219557916246574350226621065864892544379695004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4708495385570554893/3125000000000000000)
  centralHi := (150671852338257756577/100000000000000000000)
  directionLo := (30708410057034294047/20000000000000000000)
  directionHi := (38385512571292867559/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree028.table
  base := (-3395221586088508364438405219258962093397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-12400117526016361227114703842180000000000000)
      constant := (115881791908668610459109697720422824874590884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree028.table
  base := (-3396172401119133275038187133359751097037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-25024664816269062377895871077240000000000000)
      constant := (236231192684369320304222538347652849550417928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30708410057034294047/20000000000000000000)
  centralHi := (38385512571292867559/25000000000000000000)
  directionLo := (156359570620114262773/100000000000000000000)
  directionHi := (78179785310057131387/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree029.table
  base := (-1375998049606309220842446625275986575207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-12824931008320861796911938121560000000000000)
      constant := (124361039714264122930682476705175748063700510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree029.table
  base := (-6881516243117517896824040983169780527123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-25882307129600789943335570471460000000000000)
      constant := (253508833765753615875491873598329185090994556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156359570620114262773/100000000000000000000)
  centralHi := (78179785310057131387/50000000000000000000)
  directionLo := (159127211510913099131/100000000000000000000)
  directionHi := (39781802877728274783/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree030.table
  base := (-6961883768859068880365997644460824379363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-13249744490625362366709172400940000000000000)
      constant := (133136703539556232019456911135716724079325918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree030.table
  base := (-1392621772732847011258324241000240170807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-26739949442932517508775269865680000000000000)
      constant := (271390099358403668018962966793307564668017020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159127211510913099131/100000000000000000000)
  centralHi := (39781802877728274783/25000000000000000000)
  directionLo := (161847531837749225819/100000000000000000000)
  directionHi := (8092376591887461291/5000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree031.table
  base := (-70364179442064595014353584780361054867/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-13674557972929862936506406680320000000000000)
      constant := (142208485056064407039118384963976389036486200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree031.table
  base := (-7037401912868233088519404600871292382421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-27597591756264245074214969259900000000000000)
      constant := (289874423145368131792874110484550519048450212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161847531837749225819/100000000000000000000)
  centralHi := (8092376591887461291/5000000000000000000)
  directionLo := (82261439448722911753/50000000000000000000)
  directionHi := (164522878897445823507/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree032.table
  base := (-3551909419424641270434036186521988170831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-14099371455234363506303640959700000000000000)
      constant := (151576155034106225512190872849573407989554732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree032.table
  base := (-1420921899587804134214873157833666720063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-28455234069595972639654668654120000000000000)
      constant := (308961370917226123599119480145966619458561180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82261439448722911753/50000000000000000000)
  centralHi := (164522878897445823507/100000000000000000000)
  directionLo := (167155412115300649773/100000000000000000000)
  directionHi := (83577706057650324887/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree033.table
  base := (-1432852100469715556950935412351253214829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-14524184937538864076100875239080000000000000)
      constant := (161239536987426793095578569531984146200816970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree033.table
  base := (-1432979222759255704766026883382787755333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-29312876382927700205094368048340000000000000)
      constant := (328650609078280530937795354853396032160923380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167155412115300649773/100000000000000000000)
  centralHi := (83577706057650324887/50000000000000000000)
  directionLo := (169747123445931696363/100000000000000000000)
  directionHi := (42436780861482924091/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree034.table
  base := (-7217877201498163251618089061721954711153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-14948998419843364645898109518460000000000000)
      constant := (171198494769497178318499237662413937922890858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree034.table
  base := (-36091941966045988678402269261570641579/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-30170518696259427770534067442560000000000000)
      constant := (348941880817275434280625223056116947775557600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169747123445931696363/100000000000000000000)
  centralHi := (42436780861482924091/25000000000000000000)
  directionLo := (172299855011258640349/100000000000000000000)
  directionHi := (3445997100225172807/2000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree035.table
  base := (-3632386357837085950230271576360599756809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-15373811902147865215695343797840000000000000)
      constant := (181452923148029982360524611174165703693191348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree035.table
  base := (-7265184015479987808980766416658207824041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-31028161009591155335973766836780000000000000)
      constant := (369834988040585952756832247726554654532844852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172299855011258640349/100000000000000000000)
  centralHi := (3445997100225172807/2000000000000000000)
  directionLo := (1748153144196272187/1000000000000000000)
  directionHi := (174815314419627218701/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree036.table
  base := (-1461005482878886700641238106209277370667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-15798625384452365785492578077220000000000000)
      constant := (192002740628334125832923600754198963730718310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree036.table
  base := (-7305358474618986325164583304823149908993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-31885803322922882901413466231000000000000000)
      constant := (391329777646359121751269268161498651984562196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1748153144196272187/1000000000000000000)
  centralHi := (174815314419627218701/100000000000000000000)
  directionLo := (88647544064070803721/50000000000000000000)
  directionHi := (177295088128141607443/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree037.table
  base := (-293548146279614338216954703424540692703/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-16223438866756866355289812356600000000000000)
      constant := (202847883978047558594589406304152893439978950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree037.table
  base := (-7338970231826932297759577842217242677889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-32743445636254610466853165625220000000000000)
      constant := (413426131075279842544502162857020931849241108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88647544064070803721/50000000000000000000)
  centralHi := (177295088128141607443/100000000000000000000)
  directionLo := (35948130629059349811/20000000000000000000)
  directionHi := (351055963174407713/195312500000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree038.table
  base := (-3682924960184089093452098041846081807117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-16648252349061366925087046635980000000000000)
      constant := (213988304041587361975714337352016146095166724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree038.table
  base := (-28773690023288177512747966658617249093/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-33601087949586338032292865019440000000000000)
      constant := (436123956339584197167473536517389000022885376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35948130629059349811/20000000000000000000)
  centralHi := (351055963174407713/195312500000000000)
  directionLo := (45538346829780619179/25000000000000000000)
  directionHi := (182153387319122476717/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree039.table
  base := (-7386503960698019834605049639312098012201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (24046046168179277535692506380000000000000)
      linear := (-1313312756258912884221867762720000000000000)
      constant := (17340304810322848235340239234858656355048322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree039.table
  base := (-1846669244465951198079241675687094123801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (1819)
      previous := (0)
      next := (833)
      square := (48092092336358555071385012760000000000000)
      linear := (-2650671558686005045979428031820000000000000)
      constant := (35340244763868312869080314852478753266748176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45538346829780619179/25000000000000000000)
  centralHi := (182153387319122476717/100000000000000000000)
  directionLo := (92267289207175995913/50000000000000000000)
  directionHi := (184534578414351991827/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree040.table
  base := (-3700347619933927227500808126054662139981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-17497879313670368064681515194740000000000000)
      constant := (237154829581522151194449883775961145180118532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree040.table
  base := (-1480166938268516578397690473511631025303/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-35316372576249793163172263807880000000000000)
      constant := (483323752150785672258759091370992061403427580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92267289207175995913/50000000000000000000)
  centralHi := (184534578414351991827/100000000000000000000)
  directionLo := (186885432148402083679/100000000000000000000)
  directionHi := (1168033950927513023/625000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree041.table
  base := (-7408446791266877011345428543308737383883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-17922692795974868634478749474120000000000000)
      constant := (249180881827706090688057604442489940292742638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree041.table
  base := (-7408559218938356206030644149110248134467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-36174014889581520728611963202100000000000000)
      constant := (507825623535885388165128040188221916783300924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186885432148402083679/100000000000000000000)
  centralHi := (1168033950927513023/625000000000000000)
  directionLo := (473017698321290181/250000000000000000)
  directionHi := (189207079328516072401/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree042.table
  base := (-1481955331433308584874251162347954533351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-18347506278279369204275983753500000000000000)
      constant := (261502100977885589743621215983735870515910430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree042.table
  base := (-7409867319560319126403282542495920077011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-37031657202913248294051662596320000000000000)
      constant := (532928762098519368790256585809868274083821692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473017698321290181/250000000000000000)
  centralHi := (189207079328516072401/100000000000000000000)
  directionLo := (95750291104987964171/50000000000000000000)
  directionHi := (191500582209975928343/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree043.table
  base := (-1480939799623487296840791073823211362837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-18772319760583869774073218032880000000000000)
      constant := (274118472673262355890954113085621318390416410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree043.table
  base := (-7404772124293122998526557540413349120517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-37889299516244975859491361990540000000000000)
      constant := (558633141208847941205632582930739227983591524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95750291104987964171/50000000000000000000)
  centralHi := (191500582209975928343/100000000000000000000)
  directionLo := (193766940176832342907/100000000000000000000)
  directionHi := (48441735044208085727/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree044.table
  base := (-7393224950751113888878766574093115188733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-19197133242888370343870452312260000000000000)
      constant := (287029985621291991145248563038469581198624738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree044.table
  base := (-7393283943469911838368997605158372744301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-38746941829576703424931061384760000000000000)
      constant := (584938739957515489346871855829298820074557572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193766940176832342907/100000000000000000000)
  centralHi := (48441735044208085727/25000000000000000000)
  directionLo := (39201418966269319963/20000000000000000000)
  directionHi := (24500886853918324977/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree045.table
  base := (-7375363292212688981060342628599689129253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-19621946725192870913667686591640000000000000)
      constant := (300236630921949350070042607495524915222937458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree045.table
  base := (-460963180663540083257537190925850161367/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-39604584142908430990370760778980000000000000)
      constant := (611845541890291375082381100084475513963963584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39201418966269319963/20000000000000000000)
  centralHi := (24500886853918324977/12500000000000000000)
  directionLo := (198221934565670289597/100000000000000000000)
  directionHi := (99110967282835144799/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree046.table
  base := (-7351120955693580127664279842280614870551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-20046760207497371483464920871020000000000000)
      constant := (313738401544978334441283831798807456521261286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree046.table
  base := (-3675579682825693295267016363117876240219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-40462226456240158555810460173200000000000000)
      constant := (639353534028141742087553874903123893969671736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198221934565670289597/100000000000000000000)
  centralHi := (99110967282835144799/50000000000000000000)
  directionLo := (25051537334840241583/12500000000000000000)
  directionHi := (40082459735744386533/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree047.table
  base := (-7320503431094679484653254863538922235049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-20471573689801872053262155150400000000000000)
      constant := (327535291923619439612826081826836532853660314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree047.table
  base := (-7320534429710010694655945424000505859449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-41319868769571886121250159567420000000000000)
      constant := (667462706107083060034027604901564474117037428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25051537334840241583/12500000000000000000)
  centralHi := (40082459735744386533/20000000000000000000)
  directionLo := (202578981092367092331/100000000000000000000)
  directionHi := (50644745273091773083/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree048.table
  base := (-3641757538456303916604977711233718852983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-20896387172106372623059389429780000000000000)
      constant := (341627297638357092112550112221298018166150476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree048.table
  base := (-7283540096371744187666310825854897572987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-42177511082903613686689858961640000000000000)
      constant := (696173049987576649380233295349326267721982364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202578981092367092331/100000000000000000000)
  centralHi := (50644745273091773083/25000000000000000000)
  directionLo := (102361366856780980157/50000000000000000000)
  directionHi := (40944546742712392063/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree049.table
  base := (-7240159363394207020165148931564750331583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-21321200654410873192856623709160000000000000)
      constant := (356014415170360994307769524825918343163774838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree049.table
  base := (-7240179558280880869125352353355626035317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-43035153396235341252129558355860000000000000)
      constant := (725484559194939882300662813147492290400377124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102361366856780980157/50000000000000000000)
  centralHi := (40944546742712392063/20000000000000000000)
  directionLo := (4136885389656637507/2000000000000000000)
  directionHi := (206844269482831875351/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree050.table
  base := (-719043906238776923978180093220904789157/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-21746014136715373762653857988540000000000000)
      constant := (370696641708976977913501672581740025437948020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree050.table
  base := (-7190455363758794880815214724151406726627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-43892795709567068817569257750080000000000000)
      constant := (755397228561177012035781968808670947158400444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4136885389656637507/2000000000000000000)
  centralHi := (206844269482831875351/100000000000000000000)
  directionLo := (26118033143015726527/12500000000000000000)
  directionHi := (208944265144125812217/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree051.table
  base := (-7134356395788188211290071909549193404833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-22170827619019874332451092267920000000000000)
      constant := (385673975001203620698447172756822117887499338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree051.table
  base := (-7134369554639641609766693866357943801351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-44750438022898796383008957144300000000000000)
      constant := (785911053945448371460692308190643589970860172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26118033143015726527/12500000000000000000)
  centralHi := (208944265144125812217/100000000000000000000)
  directionLo := (105511681883276701703/50000000000000000000)
  directionHi := (211023363766553403407/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree052.table
  base := (-353595657588339480502549767004472432693/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (24046046168179277535692506380000000000000)
      linear := (-1738126238563413454019102042100000000000000)
      constant := (30842031787218092186753072108153023004998920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree052.table
  base := (-707192377399204156969932796248427114461/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (1819)
      previous := (0)
      next := (833)
      square := (48092092336358555071385012760000000000000)
      linear := (-3508313872017732611419127426040000000000000)
      constant := (62848156308893138321043892912252453701440840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105511681883276701703/50000000000000000000)
  centralHi := (211023363766553403407/100000000000000000000)
  directionLo := (213082177044640452903/100000000000000000000)
  directionHi := (26635272130580056613/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree053.table
  base := (-3501555387949177053170165668600848827563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-23020454583628875472045560826680000000000000)
      constant := (416513954941058883501870345774282478577702236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree053.table
  base := (-218847479700571850770311902827864195081/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-46465722649562251513888355932740000000000000)
      constant := (848742160077258818721350107870080425196023424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213082177044640452903/100000000000000000000)
  centralHi := (26635272130580056613/12500000000000000000)
  directionLo := (53780321850106030297/25000000000000000000)
  directionHi := (215121287400424121189/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree054.table
  base := (-3463975221349470504935600853303386326889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-23445268065933376041842795106060000000000000)
      constant := (432376598931915391780639292350700732529069108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree054.table
  base := (-6927957364109194623246169210160976178987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-47323364962893979079328055326960000000000000)
      constant := (881059435939765531165414204639803540309014364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53780321850106030297/25000000000000000000)
  centralHi := (215121287400424121189/100000000000000000000)
  directionLo := (217141249907861239447/100000000000000000000)
  directionHi := (27142656238482654931/12500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree055.table
  base := (-6846433111855701609452544696489685025327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-23870081548237876611640029385440000000000000)
      constant := (448534344233281951857244513751584459384318422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree055.table
  base := (-6846438698667829328860493253412443163057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-48181007276225706644767754721180000000000000)
      constant := (913977857811183845535243264695317065265320404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217141249907861239447/100000000000000000000)
  centralHi := (27142656238482654931/12500000000000000000)
  directionLo := (219142594057569337027/100000000000000000000)
  directionHi := (54785648514392334257/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree056.table
  base := (-6758559572478206470772867505405534285989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-24294895030542377181437263664820000000000000)
      constant := (464987190045001459178077863677598788234007154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree056.table
  base := (-6758564081818307315068612519877202857113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-49038649589557434210207454115400000000000000)
      constant := (947497424215689278972425850571369032605774836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219142594057569337027/100000000000000000000)
  centralHi := (54785648514392334257/25000000000000000000)
  directionLo := (44225165075559864407/20000000000000000000)
  directionHi := (55281456344449830509/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree057.table
  base := (-833041309745580109474786600341241337073/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-24719708512846877751234497944200000000000000)
      constant := (481735135704528153867225693741996850273663824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree057.table
  base := (-83304176467772543614876887277302308659/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-49896291902889161775647153509620000000000000)
      constant := (981618133928651368764917764851467973443163840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44225165075559864407/20000000000000000000)
  centralHi := (55281456344449830509/25000000000000000000)
  directionLo := (22309142692570096531/10000000000000000000)
  directionHi := (223091426925700965311/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree058.table
  base := (-1640936593376443269149001093819136294769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-25144521995151378321031732223580000000000000)
      constant := (498778180659038596917091879584949583188416936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree058.table
  base := (-6563749310686321152545034042255089763447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-50753934216220889341086852903840000000000000)
      constant := (1016339985925508284217642198820516677959729484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22309142692570096531/10000000000000000000)
  centralHi := (223091426925700965311/100000000000000000000)
  directionLo := (225039860661345390539/100000000000000000000)
  directionHi := (11251993033067269527/5000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree059.table
  base := (-3228403858903416171250398992550493011319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-25569335477455878890828966502960000000000000)
      constant := (516116324443405685848570938303732600173045068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree059.table
  base := (-645681008804092976740946157191792525573/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-51611576529552616906526552298060000000000000)
      constant := (1051662979341461872461103019138447947581379560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225039860661345390539/100000000000000000000)
  centralHi := (11251993033067269527/5000000000000000000)
  directionLo := (226971568715577510349/100000000000000000000)
  directionHi := (4539431374311550207/2000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree060.table
  base := (-3171757450131610213091159611138964264133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-25994148959760379460626200782340000000000000)
      constant := (533749566662782483284455849270010180472338276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree060.table
  base := (-6343516812822806251541683250608282525483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-52469218842884344471966251692280000000000000)
      constant := (1087587113439664338706086495455366403038320476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226971568715577510349/100000000000000000000)
  centralHi := (4539431374311550207/2000000000000000000)
  directionLo := (228886974561556251497/100000000000000000000)
  directionHi := (114443487280778125749/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree061.table
  base := (-6223868254557973798870285538208487405011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-26418962442064880030423435061720000000000000)
      constant := (551677906978814390242919678988061593771318846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree061.table
  base := (-6223869797674760103598310043092944469667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-53326861156216072037405951086500000000000000)
      constant := (1124112387586076065289317020734725008615515324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228886974561556251497/100000000000000000000)
  centralHi := (114443487280778125749/50000000000000000000)
  directionLo := (46157296819755323953/20000000000000000000)
  directionHi := (115393242049388309883/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree062.table
  base := (-152446701735997914862140641253127522423/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-26843775924369380600220669341100000000000000)
      constant := (569901345098710099052166605738613147690523120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree062.table
  base := (-6097869314355822552339043994086718316837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-54184503469547799602845650480720000000000000)
      constant := (1161238801229569736878869919229842135253454564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46157296819755323953/20000000000000000000)
  centralHi := (115393242049388309883/50000000000000000000)
  directionLo := (116335243328717081147/50000000000000000000)
  directionHi := (46534097331486832459/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree063.table
  base := (-745689324659783251400238559659992117257/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-27268589406673881170017903620480000000000000)
      constant := (588419880766567223473248630637543143944811216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree063.table
  base := (-596551560151540308163031444095058582331/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-55042145782879527168285349874940000000000000)
      constant := (1198966353886164351041464072244549711950327320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116335243328717081147/50000000000000000000)
  centralHi := (46534097331486832459/20000000000000000000)
  directionLo := (2931741949127142427/1250000000000000000)
  directionHi := (234539355930171394161/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree064.table
  base := (-582680806086186551115868067012490682589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-27693402888978381739815137899860000000000000)
      constant := (607233513756477876235556253381293344478547540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree064.table
  base := (-5826808870862819007951112732644087892223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-55899788096211254733725049269160000000000000)
      constant := (1237295045126513412259280085323157789754571756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2931741949127142427/1250000000000000000)
  centralHi := (234539355930171394161/100000000000000000000)
  directionLo := (236393450837522143257/100000000000000000000)
  directionHi := (118196725418761071629/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree065.table
  base := (-568174865881133679690789490593562339813/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (24046046168179277535692506380000000000000)
      linear := (-2162939720867914023816336321480000000000000)
      constant := (48180172605156980533284753381162021374945860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree065.table
  base := (-5681749312071242812885592927155447422671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (1819)
      previous := (0)
      next := (833)
      square := (48092092336358555071385012760000000000000)
      linear := (-4365956185349460176858826820260000000000000)
      constant := (98171144197381517441512714925851250202063324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236393450837522143257/100000000000000000000)
  centralHi := (118196725418761071629/50000000000000000000)
  directionLo := (47646623266546129279/20000000000000000000)
  directionHi := (59558279083182661599/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree066.table
  base := (-1382584142473537581609985290555976445759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-28543029853587382879409606458620000000000000)
      constant := (645746070916985620520282996921784959536001496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree066.table
  base := (-5530337096682534216402660769812228662927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-57615072722874709864604448057600000000000000)
      constant := (1315755841856616402970522757531750800271584044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47646623266546129279/20000000000000000000)
  centralHi := (59558279083182661599/25000000000000000000)
  directionLo := (60014671037764147507/25000000000000000000)
  directionHi := (240058684151056590029/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree067.table
  base := (-5372571956471178076712138163109061434013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-28967843335891883449206840738000000000000000)
      constant := (665444994741678572813665141095072411705910818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree067.table
  base := (-5372572381222574306460200499921659607763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-58472715036206437430044147451820000000000000)
      constant := (1355887946681048954105473886572896374315456636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60014671037764147507/25000000000000000000)
  centralHi := (240058684151056590029/100000000000000000000)
  directionLo := (48374094701635140129/20000000000000000000)
  directionHi := (120935236754087850323/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree068.table
  base := (-5208454967255030707210569626912270745089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-29392656818196384019004075017380000000000000)
      constant := (685439015190325016604129337584590957464479754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree068.table
  base := (-1041691061938428384940966517152477513009/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-59330357349538164995483846846040000000000000)
      constant := (1396621188747223800653659334849833878018088740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48374094701635140129/20000000000000000000)
  centralHi := (120935236754087850323/50000000000000000000)
  directionLo := (121834395875919927343/50000000000000000000)
  directionHi := (243668791751839854687/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree069.table
  base := (-1007597147904506089822561135463091211827/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-29817470300500884588801309296760000000000000)
      constant := (705728132123726254149261530284927127556037110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree069.table
  base := (-629748251945422961775525743773350742327/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-60187999662869892560923546240260000000000000)
      constant := (1437955567784459429263497910347018657556486752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121834395875919927343/50000000000000000000)
  centralHi := (243668791751839854687/100000000000000000000)
  directionLo := (61363483742641006333/25000000000000000000)
  directionHi := (245453934970564025333/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree070.table
  base := (-4861164400893799466348654006927447847823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-30242283782805385158598543576140000000000000)
      constant := (726312345412475481574836894195775567882307478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree070.table
  base := (-4861164623384440331116013533335999482157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-61045641976201620126363245634480000000000000)
      constant := (1479891083540172210562621811781844593050185604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61363483742641006333/25000000000000000000)
  centralHi := (245453934970564025333/100000000000000000000)
  directionLo := (123613094281376849967/50000000000000000000)
  directionHi := (49445237712550739987/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree071.table
  base := (-1169497767691727454101408855513794478319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-30667097265109885728395777855520000000000000)
      constant := (747191654935503053814563083219541049595938136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree071.table
  base := (-2338995625036588182278414321793930482721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-61903284289533347691802945028700000000000000)
      constant := (1522427735777252715285982628484921317962083624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123613094281376849967/50000000000000000000)
  centralHi := (49445237712550739987/20000000000000000000)
  directionLo := (248985827769370486571/100000000000000000000)
  directionHi := (62246456942342621643/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree072.table
  base := (-70132279085601326035490836008782484001/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-31091910747414386298193012134900000000000000)
      constant := (768366060578899634774314606484214051918271104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree072.table
  base := (-897693201192789800829067260515660994787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-62760926602865075257242644422920000000000000)
      constant := (1565565524271942867012473667232371197512859820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248985827769370486571/100000000000000000000)
  centralHi := (62246456942342621643/25000000000000000000)
  directionLo := (250733118172950974659/100000000000000000000)
  directionHi := (12536655908647548733/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree073.table
  base := (-4292588879245998556570038018715278704253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-31516724229718886867990246414280000000000000)
      constant := (789835562234960705878298677528827707393887458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree073.table
  base := (-536573624457244171513873148241227073809/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-63618568916196802822682343817140000000000000)
      constant := (1609304448812111442034213606110031831954522784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250733118172950974659/100000000000000000000)
  centralHi := (12536655908647548733/5000000000000000000)
  directionLo := (126234158082770304189/50000000000000000000)
  directionHi := (252468316165540608379/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree074.table
  base := (-4090360224935954351097379087502276886877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-31941537712023387437787480693660000000000000)
      constant := (811600159801407632614226284048672691236706722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree074.table
  base := (-4090360318717120461017313911668035929033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-64476211229528530388122043211360000000000000)
      constant := (1653644509195846844298283588800547223135921076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126234158082770304189/50000000000000000000)
  centralHi := (252468316165540608379/100000000000000000000)
  directionLo := (50838333877575393357/20000000000000000000)
  directionHi := (127095834693938483393/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree075.table
  base := (-1940889997346493033033834219668747830987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-32366351194327888007584714973040000000000000)
      constant := (833659853180749756292456195071136779398758364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree075.table
  base := (-242611254389575880184773957609627096461/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-65333853542860257953561742605580000000000000)
      constant := (1698585705230302976793760915916420319974033472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50838333877575393357/20000000000000000000)
  centralHi := (127095834693938483393/50000000000000000000)
  directionLo := (255903417141952450393/100000000000000000000)
  directionHi := (127951708570976225197/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree076.table
  base := (-1833424140228847293017056640916112914813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-32791164676632388577381949252420000000000000)
      constant := (856014642279759307616051458487702123008759236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree076.table
  base := (-3666848341297198084474084086775443647533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-66191495856191985519001441999800000000000000)
      constant := (1744128036730747364839850521177699400282803076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255903417141952450393/100000000000000000000)
  centralHi := (127951708570976225197/50000000000000000000)
  directionLo := (257603790778902355443/100000000000000000000)
  directionHi := (64400947694725588861/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree077.table
  base := (-86139129259882855156606248248193703071/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-33215978158936889147179183531800000000000000)
      constant := (878664527009036739009610792475018263403440240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree077.table
  base := (-3445565219388752048352197319566787357141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-67049138169523713084441141394020000000000000)
      constant := (1790271503519771218242670952487556055239718052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257603790778902355443/100000000000000000000)
  centralHi := (64400947694725588861/25000000000000000000)
  directionLo := (2025726672374987517/781250000000000000)
  directionHi := (259293014063998402177/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree078.table
  base := (-3217930749252772542204085202057742098321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (24046046168179277535692506380000000000000)
      linear := (-2587753203172414593613570600860000000000000)
      constant := (69354577483280666605467072778399496116330962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree078.table
  base := (-402241348587713694516243867612759636737/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (1819)
      previous := (0)
      next := (833)
      square := (48092092336358555071385012760000000000000)
      linear := (-5223598498681187742298526214480000000000000)
      constant := (141308931186663803269143127355589275973352224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2025726672374987517/781250000000000000)
  centralHi := (259293014063998402177/100000000000000000000)
  directionLo := (260971303520377979821/100000000000000000000)
  directionHi := (130485651760188989911/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree079.table
  base := (-1491972549329059328224703630046654155693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-34065605123545890286773652090560000000000000)
      constant := (924849583017824246450962790224090385372254596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree079.table
  base := (-1491972565208973766876108846882450558113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-68764422796187168215320540182460000000000000)
      constant := (1884361842286685191202603428660242280536293672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260971303520377979821/100000000000000000000)
  centralHi := (130485651760188989911/50000000000000000000)
  directionLo := (262638868753003928141/100000000000000000000)
  directionHi := (131319434376501964071/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree080.table
  base := (-1371804148686724144667560780711483921267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-34490418605850390856570886369940000000000000)
      constant := (948384754134698715668583730655917110607670524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree080.table
  base := (-342951040367460885595076138743056992003/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-69622065109518895780760239576680000000000000)
      constant := (1932308713940938759955916883413832643361743328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262638868753003928141/100000000000000000000)
  centralHi := (131319434376501964071/50000000000000000000)
  directionLo := (66073978188556763199/25000000000000000000)
  directionHi := (264295912754227052797/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree081.table
  base := (-2496920421510197482197734376181426679219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-34915232088154891426368120649320000000000000)
      constant := (972215020556095077378019550056757033347271934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree081.table
  base := (-499384088417626583699272197913273390237/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-70479707422850623346199938970900000000000000)
      constant := (1980856720235624745608256993680776907822996820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66073978188556763199/25000000000000000000)
  centralHi := (264295912754227052797/100000000000000000000)
  directionLo := (66485658048053102791/25000000000000000000)
  directionHi := (53188526438442482233/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree082.table
  base := (-560970386178470957845867979078340711441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-35340045570459391996165354928700000000000000)
      constant := (996340382207336776736575175047698250074395304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree082.table
  base := (-2243881561274767658333714544894379870049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-71337349736182350911639638365120000000000000)
      constant := (2030005861021864661399420798282604197623540628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66485658048053102791/25000000000000000000)
  centralHi := (53188526438442482233/20000000000000000000)
  directionLo := (267579217683389507419/100000000000000000000)
  directionHi := (13378960884169475371/5000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree083.table
  base := (-496122934580987814016018311516698837831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-35764859052763892565962589208080000000000000)
      constant := (1020760839016085617610210462217593269513757464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree083.table
  base := (-62015367239073137604715873520648267621/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-72194992049514078477079337759340000000000000)
      constant := (2079756136155364788156477630196901510024467584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267579217683389507419/100000000000000000000)
  centralHi := (13378960884169475371/5000000000000000000)
  directionLo := (269205854049994839717/100000000000000000000)
  directionHi := (134602927024997419859/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree084.table
  base := (-859375535756621479367351392209211081779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-36189672535068393135759823487460000000000000)
      constant := (1045476390912200336991595314845599719926152188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree084.table
  base := (-859375541117788028403710556841731704741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-73052634362845806042519037153560000000000000)
      constant := (2130107545496151095775617264184809936205570504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269205854049994839717/100000000000000000000)
  centralHi := (134602927024997419859/50000000000000000000)
  directionLo := (13541136028184590431/5000000000000000000)
  directionHi := (270822720563691808621/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree085.table
  base := (-1446659611410727669473271792532045997177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-36614486017372893705557057766840000000000000)
      constant := (1070487037827612160588430730912897505358862522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree085.table
  base := (-361664905009206997114870501771885931553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-73910276676177533607958736547780000000000000)
      constant := (2181060088908334699622974069904663961323242064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13541136028184590431/5000000000000000000)
  centralHi := (270822720563691808621/100000000000000000000)
  directionLo := (136214995588088495337/50000000000000000000)
  directionHi := (10897199647047079627/4000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree086.table
  base := (-584108711605194196772250212808234868349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-37039299499677394275354292046220000000000000)
      constant := (1095792779696214389633378284182104899686988228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree086.table
  base := (-292054357537314505588837048701690272111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-74767918989509261173398435942000000000000000)
      constant := (2232613766259902611519378181020861888512635568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136214995588088495337/50000000000000000000)
  centralHi := (10897199647047079627/4000000000000000000)
  directionLo := (274027834737612463541/100000000000000000000)
  directionHi := (137013917368806231771/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree087.table
  base := (-883424570268612803550520038218507146073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-37464112981981894845151526325600000000000000)
      constant := (1121393616453763647026419413459711433753881978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree087.table
  base := (-883424575849620133384160350927804899697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-75625561302840988738838135336220000000000000)
      constant := (2284768577422529574403754420246355911663414484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274027834737612463541/100000000000000000000)
  centralHi := (137013917368806231771/50000000000000000000)
  directionLo := (68904103800915145017/25000000000000000000)
  directionHi := (275616415203660580069/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree088.table
  base := (-296140557095985046231987859738457999353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-37888926464286395414948760604980000000000000)
      constant := (1147289548037790871605879856625330407177312116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree088.table
  base := (-59228111868032039798820213297683860453/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-76483203616172716304277834730440000000000000)
      constant := (2337524522271407588753077836323682971310013160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68904103800915145017/25000000000000000000)
  centralHi := (275616415203660580069/100000000000000000000)
  directionLo := (34649486478979967599/12500000000000000000)
  directionHi := (277195891831839740793/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree089.table
  base := (-36848389364612090774767133517529419331/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-38313739946590895984745994884360000000000000)
      constant := (1173480574387520516795323558305830801350386928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree089.table
  base := (-73696779631526042012072486338942794573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-77340845929504443869717534124660000000000000)
      constant := (2390881600685090390993734133584715996050423824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34649486478979967599/12500000000000000000)
  centralHi := (277195891831839740793/100000000000000000000)
  directionLo := (139383209683933391713/50000000000000000000)
  directionHi := (278766419367866783427/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree090.table
  base := (4528684608737885577573453865724542777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-38738553428895396554543229163740000000000000)
      constant := (1199966695443796703229321383607039689372751756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree090.table
  base := (2264341578883724104924693107545079239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-78198488242836171435157233518880000000000000)
      constant := (2444839812545350663983211112582138405682786768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139383209683933391713/50000000000000000000)
  centralHi := (278766419367866783427/100000000000000000000)
  directionLo := (280328148222603125519/100000000000000000000)
  directionHi := (3504101852782539069/1250000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree091.table
  base := (39906535175293633928105375226075885237/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (24046046168179277535692506380000000000000)
      linear := (-3012566685476915163410804880240000000000000)
      constant := (94365223934539639184854454219826071352387888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree091.table
  base := (79813069767333465399964005857661016303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (1819)
      previous := (0)
      next := (833)
      square := (48092092336358555071385012760000000000000)
      linear := (-6081240812012915307738225608700000000000000)
      constant := (192261473672080628807056162453702680474173072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280328148222603125519/100000000000000000000)
  centralHi := (3504101852782539069/1250000000000000000)
  directionLo := (70470306160044335929/25000000000000000000)
  directionHi := (281881224640177343717/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree092.table
  base := (317898783148662696587605904952374153069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-39588180393504397694137697722500000000000000)
      constant := (1253824221447061171966307282302083414782423932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree092.table
  base := (317898782210950502127721586047900768341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-79913772869499626566036632307320000000000000)
      constant := (2554559636148007364104567025579810285516391096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70470306160044335929/25000000000000000000)
  centralHi := (281881224640177343717/100000000000000000000)
  directionLo := (70856447714454018589/25000000000000000000)
  directionHi := (283425790857816074357/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree093.table
  base := (479346584986422601831908439886804419599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-40012993875808898263934932001880000000000000)
      constant := (1281195626283249717552718685377495439362946772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree093.table
  base := (958693168465421932825284515223874712243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-80771415182831354131476331701540000000000000)
      constant := (2610321247668903185235635789301071517916428804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70856447714454018589/25000000000000000000)
  centralHi := (283425790857816074357/100000000000000000000)
  directionLo := (142480992628938819457/50000000000000000000)
  directionHi := (56992397051575527783/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree094.table
  base := (1287939039856445425347805742105724001059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-40437807358113398833732166281260000000000000)
      constant := (1308862125604272468601713661680095204137073826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree094.table
  base := (1287939038644940379510933351502135870771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-81629057496163081696916031095760000000000000)
      constant := (2666683992193154186573841153151656331545923588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142480992628938819457/50000000000000000000)
  centralHi := (56992397051575527783/20000000000000000000)
  directionLo := (57297988502509666299/20000000000000000000)
  directionHi := (35811242814068541437/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree095.table
  base := (1623535124682383851991326924118701933401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-40862620840417899403529400560640000000000000)
      constant := (1336823719358145962516169057816481363760468614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree095.table
  base := (1623535123708806898965679329331432766499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-82486699809494809262355730489980000000000000)
      constant := (2723647869616822023044019988538521645650459972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57297988502509666299/20000000000000000000)
  centralHi := (35811242814068541437/12500000000000000000)
  directionLo := (288009793721629582301/100000000000000000000)
  directionHi := (144004896860814791151/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree096.table
  base := (982740687222126206681520449204941829309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-41287434322722399973326634840020000000000000)
      constant := (1365080407494163701512870295505867622029838652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree096.table
  base := (982740686830978237851387768515860289769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-83344342122826536827795429884200000000000000)
      constant := (2781212879838516702794765172724780329335303064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288009793721629582301/100000000000000000000)
  centralHi := (144004896860814791151/50000000000000000000)
  directionLo := (289521666543814985929/100000000000000000000)
  directionHi := (28952166654381498593/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree097.table
  base := (2313777740350264004254909897126388098427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-41712247805026900543123869119400000000000000)
      constant := (1393632189962850813467136424451651157531804978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree097.table
  base := (144611108732608169725614333455948415741/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-84201984436158264393235129278420000000000000)
      constant := (2839379022759306994602816773437916114193963968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289521666543814985929/100000000000000000000)
  centralHi := (28952166654381498593/10000000000000000000)
  directionLo := (36378210665228654477/12500000000000000000)
  directionHi := (291025685321829235817/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree098.table
  base := (667106043695236951063127404716023301737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-42137061287331401112921103398780000000000000)
      constant := (1422479066715921154967067218412208190511845272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree098.table
  base := (2668424174276004529476497040437822273431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-85059626749489991958674828672640000000000000)
      constant := (2898146298282635508787256213687417903570518068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36378210665228654477/12500000000000000000)
  centralHi := (291025685321829235817/100000000000000000000)
  directionLo := (292521971201776137103/100000000000000000000)
  directionHi := (18282623200111008569/6250000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree099.table
  base := (9466939472653214811276612644134187953/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-42561874769635901682718337678160000000000000)
      constant := (1451621037706236629087882890833793661306989440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree099.table
  base := (1514710315421706557357339529183585023571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-85917269062821719524114528066860000000000000)
      constant := (2957514706314238037528434827496466120855603976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292521971201776137103/100000000000000000000)
  centralHi := (18282623200111008569/6250000000000000000)
  directionLo := (147005321123509949861/50000000000000000000)
  directionHi := (294010642247019899723/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree100.table
  base := (1698383532180649936291642213804128166707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-42986688251940402252515571957540000000000000)
      constant := (1481058102887768523994715441938594771922081796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree100.table
  base := (3396767064035504279056500780283432833569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-86774911376153447089554227461080000000000000)
      constant := (3017484246762066799780433365158414801786477932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147005321123509949861/50000000000000000000)
  centralHi := (294010642247019899723/100000000000000000000)
  directionLo := (295491813546902679071/100000000000000000000)
  directionHi := (9234119173340708721/3125000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree101.table
  base := (377046342978232355600343333987621675587/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-43411501734244902822312806236920000000000000)
      constant := (1510790262215560705913331062963239483790452180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree101.table
  base := (3770463429520665057386477230523139584141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-87632553689485174654993926855300000000000000)
      constant := (3078054919536217284449997623142618427076637948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295491813546902679071/100000000000000000000)
  centralHi := (9234119173340708721/3125000000000000000)
  directionLo := (74241399330145421491/25000000000000000000)
  directionHi := (59393119464116337193/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree102.table
  base := (4150509684199819364212597378383622684349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-43836315216549403392110040516300000000000000)
      constant := (1540817515645694522492114199387520993401929886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree102.table
  base := (1037627420997422802029819517264309663823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-88490196002816902220433626249520000000000000)
      constant := (3139226724548858425335192551519498079992932176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74241399330145421491/25000000000000000000)
  centralHi := (59393119464116337193/20000000000000000000)
  directionLo := (298432103016250997297/100000000000000000000)
  directionHi := (149216051508125498649/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree103.table
  base := (4536905785291615065008279295563696006611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-44261128698853903961907274795680000000000000)
      constant := (1571139863135255291087611519002406587750703554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree103.table
  base := (453690578512288438083167514923255373287/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-89347838316148629785873325643740000000000000)
      constant := (3200999661714165874181359843607641118970260360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298432103016250997297/100000000000000000000)
  centralHi := (149216051508125498649/50000000000000000000)
  directionLo := (149945718702998171477/50000000000000000000)
  directionHi := (59978287481199268591/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree104.table
  base := (4929651691694051995566743226085275355253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (24046046168179277535692506380000000000000)
      linear := (-3437380167781415733208039159620000000000000)
      constant := (123212100357100020139670750280034651477709734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree104.table
  base := (616206461444821899101707164771426875153/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (1819)
      previous := (0)
      next := (833)
      square := (48092092336358555071385012760000000000000)
      linear := (-6938883125344642873177925002920000000000000)
      constant := (251028748534481397344643353599154740740190944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149945718702998171477/50000000000000000000)
  centralHi := (59978287481199268591/20000000000000000000)
  directionLo := (301343704676515513153/100000000000000000000)
  directionHi := (150671852338257756577/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree105.table
  base := (1332186840742937189895968678512405672607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-45110755663462905101501743354440000000000000)
      constant := (1632669840125827957940586531243371317408093992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree105.table
  base := (5328747362862981673404741170910673100253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-91063122942812084916752724432180000000000000)
      constant := (3326348932169135589395704350718344345047313084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301343704676515513153/100000000000000000000)
  centralHi := (150671852338257756577/50000000000000000000)
  directionLo := (151394503257961261861/50000000000000000000)
  directionHi := (302789006515922523723/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree106.table
  base := (5734192759588637660820466201268751239531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-45535569145767405671298977633820000000000000)
      constant := (1663877469545748806818225295347166513756884434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree106.table
  base := (5734192759501321957754614981546778696677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-91920765256143812482192423826400000000000000)
      constant := (3389925265296621608305465673215506867196860956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151394503257961261861/50000000000000000000)
  centralHi := (302789006515922523723/100000000000000000000)
  directionLo := (152113721098420101979/50000000000000000000)
  directionHi := (304227442196840203959/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree107.table
  base := (3072993921440098560092788359061735982883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-45960382628071906241096211913200000000000000)
      constant := (1695380192862856983567437831808642200573286724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree107.table
  base := (3072993921405054038249135278478769379507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-92778407569475540047632123220620000000000000)
      constant := (3454102730252306668607775327664847388603280392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152113721098420101979/50000000000000000000)
  centralHi := (304227442196840203959/100000000000000000000)
  directionLo := (12226364346238933999/4000000000000000000)
  directionHi := (38207388581996668747/12500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree108.table
  base := (6564132575026810801712903831729927267921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-46385196110376406810893446192580000000000000)
      constant := (1727178010038803397223554309960854146249671894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree108.table
  base := (410258285935659654180268515941978265939/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-93636049882807267613071822614840000000000000)
      constant := (3518881326959494273181373451256245310773188672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12226364346238933999/4000000000000000000)
  centralHi := (38207388581996668747/12500000000000000000)
  directionLo := (307084100570342940471/100000000000000000000)
  directionHi := (38385512571292867559/12500000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree109.table
  base := (6988626919028190547575661863244263466299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-46810009592680907380690680471960000000000000)
      constant := (1759270921036069755594538369125454683154827186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree109.table
  base := (6988626918983040641997314983570696395587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-94493692196138995178511522009060000000000000)
      constant := (3584261055343149191678795659246478872290250436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307084100570342940471/100000000000000000000)
  centralHi := (38385512571292867559/12500000000000000000)
  directionLo := (308502510430351072749/100000000000000000000)
  directionHi := (1234010041721404291/400000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree110.table
  base := (3709735419339402847184883293556359336703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-47234823074985407950487914751340000000000000)
      constant := (1791658925817943650587698267897732296734833684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree110.table
  base := (3709735419321286236204343814336828719641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-95351334509470722743951221403280000000000000)
      constant := (3650241915329847696005560671512800177286863896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308502510430351072749/100000000000000000000)
  centralHi := (1234010041721404291/400000000000000000)
  directionLo := (309914428609836182003/100000000000000000000)
  directionHi := (77478607152459045501/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree111.table
  base := (982083037318033259208714827302157443611/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-47659636557289908520285149030720000000000000)
      constant := (1824342024348494610572250549901380101182572432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree111.table
  base := (1964166074628797724782789297774452001363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-96208976822802450309390920797500000000000000)
      constant := (3716823906847729717190042330860663854635056656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309914428609836182003/100000000000000000000)
  centralHi := (77478607152459045501/25000000000000000000)
  directionLo := (311319943433268698753/100000000000000000000)
  directionHi := (155659971716634349377/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree112.table
  base := (8300207263938610119044967341290094341489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-48084450039594409090082383310100000000000000)
      constant := (1857320216592551070519834636811908155662269846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree112.table
  base := (166004145278305614416008805063844402899/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-97066619136134177874830620191720000000000000)
      constant := (3784007029826452827603873870519073822453958600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311319943433268698753/100000000000000000000)
  centralHi := (155659971716634349377/50000000000000000000)
  directionLo := (312719141240228525547/100000000000000000000)
  directionHi := (78179785310057131387/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree113.table
  base := (1750019940180490622807242998522179567217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-48509263521898909659879617589480000000000000)
      constant := (1890593502515678214327960800697512450405790190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree113.table
  base := (70000797607069883780091709230563634959/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-97924261449465905440270319585940000000000000)
      constant := (3851791284197147959336227802117245381462106500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312719141240228525547/100000000000000000000)
  centralHi := (78179785310057131387/25000000000000000000)
  directionLo := (314112106447297526539/100000000000000000000)
  directionHi := (15705605322364876327/5000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree114.table
  base := (9206341576181953805544915481401079515249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-48934077004203410229676851868860000000000000)
      constant := (1924161882084156646965987115821940694628462486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree114.table
  base := (9206341576166937412104170050451723781133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-98781903762797633005710018980160000000000000)
      constant := (3920176669892376775606003529364526095828137724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314112106447297526539/100000000000000000000)
  centralHi := (15705605322364876327/5000000000000000000)
  directionLo := (157749460803746289157/50000000000000000000)
  directionHi := (63099784321498515663/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree115.table
  base := (2417233214302140110789428127040931117777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-49358890486507910799474086148240000000000000)
      constant := (1958025355264961856958994438897503016613703512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree115.table
  base := (386757314287860572457379538971666164093/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-99639546076129360571149718374380000000000000)
      constant := (3989163186846090617534524876336200974519515100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157749460803746289157/50000000000000000000)
  centralHi := (63099784321498515663/20000000000000000000)
  directionLo := (63375933493471517399/20000000000000000000)
  directionHi := (79219916866839396749/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree116.table
  base := (5068936756039749921343677261816355014931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-49783703968812411369271320427620000000000000)
      constant := (1992183922025744432298216896853243567970280068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree116.table
  base := (10137873512069837163628267928652114673329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-100497188389461088136589417768600000000000000)
      constant := (4058750834993590953495851064810986488557511212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63375933493471517399/20000000000000000000)
  centralHi := (79219916866839396749/25000000000000000000)
  directionLo := (159127211510913099131/50000000000000000000)
  directionHi := (318254423021826198263/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree117.table
  base := (10613163509538975356953755494130528327807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (24046046168179277535692506380000000000000)
      linear := (-3862193650085916303005273439000000000000000)
      constant := (155895198641139307321801067880847181209568946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree117.table
  base := (5306581754765612550980531847757258374293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (1819)
      previous := (0)
      next := (833)
      square := (48092092336358555071385012760000000000000)
      linear := (-7796525438676370438617624397140000000000000)
      constant := (317610739559345481745558840069287764612779416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159127211510913099131/50000000000000000000)
  centralHi := (318254423021826198263/100000000000000000000)
  directionLo := (63924653113392135871/20000000000000000000)
  directionHi := (79905816391740169839/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree118.table
  base := (2773700704740010426374703585850721804147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-50633330933421412508865788986380000000000000)
      constant := (2061386336161105823100200881199490527637620232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree118.table
  base := (1386850352369228226759913578685362363059/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-102212473016124543267468816557040000000000000)
      constant := (4199729524617680288634313410434601318978269216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63924653113392135871/20000000000000000000)
  centralHi := (79905816391740169839/25000000000000000000)
  directionLo := (20061641921916662769/6250000000000000000)
  directionHi := (64197254150133320861/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree119.table
  base := (11582791410327126497917982366179530918121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-51058144415725913078663023265760000000000000)
      constant := (2096430183474193125644707680711531044350974694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree119.table
  base := (231655828206442831067604916045042342833/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-103070115329456270832908515951260000000000000)
      constant := (4271120565971286601891886142361964793563266200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20061641921916662769/6250000000000000000)
  centralHi := (64197254150133320861/20000000000000000000)
  directionLo := (322343512621477496671/100000000000000000000)
  directionHi := (10073234769421171771/3125000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree120.table
  base := (603856462710958500386012203909231343001/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-51482957898030413648460257545140000000000000)
      constant := (2131769124244239948254272391286079211636060280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree120.table
  base := (6038564627107586259681878887295096117023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-103927757642787998398348215345480000000000000)
      constant := (4343112738272644414869568878516068909850645288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322343512621477496671/100000000000000000000)
  centralHi := (10073234769421171771/3125000000000000000)
  directionLo := (161847531837749225819/50000000000000000000)
  directionHi := (323695063675498451639/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree121.table
  base := (12577816321793356335796126794685281764191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-51907771380334914218257491824520000000000000)
      constant := (2167403158441999675607198007620815875708889674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree121.table
  base := (2515563264358030183779287254448484796077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-104785399956119725963787914739700000000000000)
      constant := (4415706041463260594482887066916725135832220780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161847531837749225819/50000000000000000000)
  centralHi := (323695063675498451639/100000000000000000000)
  directionLo := (162520497450796473489/50000000000000000000)
  directionHi := (325040994901592946979/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree122.table
  base := (204450821637022040029018758935885864509/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-52332584862639414788054726103900000000000000)
      constant := (2203332286038796108934312061752743249063176064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree122.table
  base := (13084852584766840445779097249875185400301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-105643042269451453529227614133920000000000000)
      constant := (4488900475485782821502868762319996875991810428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162520497450796473489/50000000000000000000)
  centralHi := (325040994901592946979/100000000000000000000)
  directionLo := (81595343956223134457/25000000000000000000)
  directionHi := (326381375824892537829/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree123.table
  base := (13598238015414437832950009113060586579037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-52757398344943915357851960383280000000000000)
      constant := (2239556507006508092854719748996948434791143518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree123.table
  base := (13598238015412377239524235677359520626459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-106500684582783181094667313528140000000000000)
      constant := (4562696040283968848020445304524782607830458852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81595343956223134457/25000000000000000000)
  centralHi := (326381375824892537829/100000000000000000000)
  directionLo := (163858137274352446259/50000000000000000000)
  directionHi := (327716274548704892519/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree124.table
  base := (14117972586528281592393393986927658357197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-53182211827248415927649194662660000000000000)
      constant := (2276075821317554668619946374704144645574197758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree124.table
  base := (2823594517305325923318471005588242546953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-107358326896114908660107012922360000000000000)
      constant := (4637092735802656806981398594574824779426103420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163858137274352446259/50000000000000000000)
  centralHi := (327716274548704892519/100000000000000000000)
  directionLo := (329045757794891647013/100000000000000000000)
  directionHi := (164522878897445823507/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree125.table
  base := (14644056271429379320494994060161282193317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-53607025309552916497446428942040000000000000)
      constant := (2312890228944880731835023884685128540144023438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree125.table
  base := (3661014067857013754430571824310174217437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-108215969209446636225546712316580000000000000)
      constant := (4712090561987736530075546983757241633251848944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329045757794891647013/100000000000000000000)
  centralHi := (164522878897445823507/50000000000000000000)
  directionLo := (66073978188556763199/20000000000000000000)
  directionHi := (82592472735695953999/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree126.table
  base := (7588244521970547624385879312944001600583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-54031838791857417067243663221420000000000000)
      constant := (2349999729861943173830710465523130435245982324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree126.table
  base := (15176489043940033691186232877371890709143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-109073611522778363790986411710800000000000000)
      constant := (4787689518786121832446386494467240194358142004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66073978188556763199/20000000000000000000)
  centralHi := (82592472735695953999/25000000000000000000)
  directionLo := (82922184516674745763/25000000000000000000)
  directionHi := (331688738066698983053/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree127.table
  base := (3143054175675702105921781624995689144481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-54456652274161917637040897500800000000000000)
      constant := (2387404324042697486895524730745193143962518670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree127.table
  base := (7857635439188829820305286495716974538849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-109931253836110091356426111105020000000000000)
      constant := (4863889606145723724733271427825265548729571544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82922184516674745763/25000000000000000000)
  centralHi := (331688738066698983053/100000000000000000000)
  directionLo := (333002361972121185749/100000000000000000000)
  directionHi := (1332009447888484743/400000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree128.table
  base := (16260401749535652299731531852403990358679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-54881465756466418206838131780180000000000000)
      constant := (2425104011461584814546105920896417646223700506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree128.table
  base := (16260401749534970313276252026572220199501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-110788896149441818921865810499240000000000000)
      constant := (4940690824015424514879287539048448462564588028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell186.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333002361972121185749/100000000000000000000)
  centralHi := (1332009447888484743/400000000000000000)
  directionLo := (167155412115300649773/50000000000000000000)
  directionHi := (334310824230601299547/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree129.table
  base := (16811881632673143974069743005507817241093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (312598600186330607964002582940000000000000)
      linear := (-55306279238770918776635366059560000000000000)
      constant := (2463098792093519428925193170758909926682468302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree129.table
  base := (8405940816336298697824114841373036193189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (23647)
      previous := (0)
      next := (10829)
      square := (625197200372661215928005165880000000000000)
      linear := (-111646538462773546487305509893460000000000000)
      constant := (5018093172345052763944585766408306534799574584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell186.Kernel129
