import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell146.Parameters
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch000_049
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch050_099
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch100_149
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch150_199
import ForestUnimodality.BinomialMassData.Q28_53.Batch000_049
import ForestUnimodality.BinomialMassData.Q28_53.Batch050_099
import ForestUnimodality.BinomialMassData.Q28_53.Batch100_149
import ForestUnimodality.BinomialMassData.Q28_53.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree000.table
  base := (75934947834368823272868099/1000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (175241026460157163502362465000000000000)
      linear := (-12585612376646137383628954000000000000)
      constant := (189837369585922058182170247500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree000.table
  base := (75934947834368823272868099/1000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (175241026460157163502362465000000000000)
      linear := (-12585612376646137383628954000000000000)
      constant := (189837369585922058182170247500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree001.table
  base := (413160406287991553790018917164601663368651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-98895529439111171490287850018535916500000000000)
      constant := (51697408325864718235777565321688000333199137679339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree001.table
  base := (413069124317731518629709799462746727304983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-2221873406798981844742502111624000000000000)
      constant := (1160935434262554660167107456852039556999697247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49919836057822463971/100000000000000000000)
  directionHi := (12479959014455615993/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree002.table
  base := (240302768203915019345182265562215778874613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-191495257867920577080493964225693809000000000000)
      constant := (30156607150897556441716559121887964335858596852757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree002.table
  base := (240211908809514352078531523081950769609843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-4302334872933967689842549296104000000000000)
      constant := (677102891671977569390587126040047711834048987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49919836057822463971/100000000000000000000)
  centralHi := (12479959014455615993/25000000000000000000)
  directionLo := (70597309184413988407/100000000000000000000)
  directionHi := (8824663648051748551/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree003.table
  base := (75505286962809880048737948201829065560263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-142047493148364991335350039216425850750000000000)
      constant := (9557682674728948563798209104127272651759301985607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree003.table
  base := (30188116442789154422076383571413435943097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-6382796339068953534942596480584000000000000)
      constant := (429162222754988464055281149885493707820797365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70597309184413988407/100000000000000000000)
  centralHi := (8824663648051748551/12500000000000000000)
  directionLo := (43231846178828679307/50000000000000000000)
  directionHi := (17292738471531471723/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree004.table
  base := (102555305398655673640275476031393906249263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-376694714725539388260906192640009594000000000000)
      constant := (13230076287928936310447033198610938415496737406607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree004.table
  base := (12813145039932059837854385463098252415763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-2115814451300984845010660916266000000000000)
      constant := (74257180465322295099548793763589982071756534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43231846178828679307/50000000000000000000)
  centralHi := (17292738471531471723/20000000000000000000)
  directionLo := (99839672115644927943/100000000000000000000)
  directionHi := (12479959014455615993/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree005.table
  base := (37245985977450133482392046456789322496491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-234647221577174396925556153423583743250000000000)
      constant := (4971949940372753212591094916003234184137681253099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree005.table
  base := (74456219802896422467685851510778054454071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-10543719271338925225142690849544000000000000)
      constant := (223259958876151229687860881504495554961485439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99839672115644927943/100000000000000000000)
  centralHi := (12479959014455615993/12500000000000000000)
  directionLo := (55812073425468075873/50000000000000000000)
  directionHi := (111624146850936151747/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree006.table
  base := (3559550798424596400528810405398845717233/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-140473542895789549860329605263581344750000000000)
      constant := (2005694750559803239820835912366830361488614895748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree006.table
  base := (11385313066401283933491385997350213677973/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-12624180737473911070242738034024000000000000)
      constant := (180138982111258564805704558007087751107130785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55812073425468075873/50000000000000000000)
  centralHi := (111624146850936151747/100000000000000000000)
  directionLo := (122278126385053966621/100000000000000000000)
  directionHi := (61139063192526983311/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree007.table
  base := (45107900217319869015254435139029656567033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-654493900011967605031524535261483271500000000000)
      constant := (6862685369717665664374092392349320737634266226137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree007.table
  base := (11271941932748144516192170159178149929261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-3676160550902224228835696304626000000000000)
      constant := (38525683502951535614231700006723423151294149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122278126385053966621/100000000000000000000)
  centralHi := (61139063192526983311/50000000000000000000)
  directionLo := (132075471698113207547/100000000000000000000)
  directionHi := (33018867924528301887/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree008.table
  base := (18269991975968628646795741116732937492597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-373546814220388505310865324734320582000000000000)
      constant := (3080659446029101120797472396854270850793122102933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree008.table
  base := (36523849729268479262199087944010222598733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-16785103669743882760442832402984000000000000)
      constant := (138364734424716713363169165977636715279840997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132075471698113207547/100000000000000000000)
  centralHi := (33018867924528301887/25000000000000000000)
  directionLo := (70597309184413988407/50000000000000000000)
  directionHi := (28238923673765595363/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree009.table
  base := (239983588354402350575698521383899960951/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-839693356869586416211936763675799056500000000000)
      constant := (5762215712361572238958144582905362639972126754875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree009.table
  base := (5996910765243837490127318052182092109181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-18865565135878868605542879587464000000000000)
      constant := (129413010030762922836637279190833483673447145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70597309184413988407/50000000000000000000)
  centralHi := (28238923673765595363/20000000000000000000)
  directionLo := (29951901634693478383/20000000000000000000)
  directionHi := (37439877043366847979/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree010.table
  base := (24802751596208315272141188670292807334519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-932293085298395821802142877882956949000000000000)
      constant := (5580455135299466181174740777665673557192898200791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree010.table
  base := (24791357905647192234844730338529607649431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-20946026602013854450642926771944000000000000)
      constant := (125341592205545964177111931254369667887251679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29951901634693478383/20000000000000000000)
  centralHi := (37439877043366847979/25000000000000000000)
  directionLo := (19732547795614989339/12500000000000000000)
  directionHi := (157860382364919914713/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree011.table
  base := (5140654497152897296745673348941512731271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-256223203431801306848087248022528710375000000000)
      constant := (1391760491170152590391853522132973713219901830519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree011.table
  base := (20552783722313328588938983993715266002579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-23026488068148840295742973956424000000000000)
      constant := (125050818558189022826883493737770182201244411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19732547795614989339/12500000000000000000)
  centralHi := (157860382364919914713/100000000000000000000)
  directionLo := (16556536579985135963/10000000000000000000)
  directionHi := (165565365799851359631/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree012.table
  base := (17035155274080769200469631395335345081623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-1117492542156014632982555106297272734000000000000)
      constant := (5691662724892031359998046774155951643796435670647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree012.table
  base := (17026602006013794285650903542600521314469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-25106949534283826140843021140904000000000000)
      constant := (127860267068689618329554897097052864372343421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16556536579985135963/10000000000000000000)
  centralHi := (165565365799851359631/100000000000000000000)
  directionLo := (172927384715314717229/100000000000000000000)
  directionHi := (17292738471531471723/10000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree013.table
  base := (878721161170996051244716635005754544319/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-302523067646206009643190305126107656625000000000)
      constant := (1483551184846954280602402585388472082085504221964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree013.table
  base := (3513018988162053542435228782177578359177/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-6796852750104702996485767081346000000000000)
      constant := (33329607013582449218514544592344817610928193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172927384715314717229/100000000000000000000)
  centralHi := (17292738471531471723/10000000000000000000)
  directionLo := (89994264284617514071/50000000000000000000)
  directionHi := (179988528569235028143/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree014.table
  base := (720145485283968789241148227125654645081/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-325672999753408361040741833677897129750000000000)
      constant := (1570120310618349310324885786788059513582849894436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree014.table
  base := (5757906618540071074572154996841185477387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-14633936233276898915521557754932000000000000)
      constant := (70553391236900640693891785326254890005980083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89994264284617514071/50000000000000000000)
  centralHi := (179988528569235028143/100000000000000000000)
  directionLo := (186782923332295572483/100000000000000000000)
  directionHi := (46695730833073893121/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree015.table
  base := (1867919517497444830486585855616096605741/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-1395291727442442849753173448918746411500000000000)
      constant := (6719996586017900875793193071691275290708644631745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree015.table
  base := (2333478919866697173053444503672437636079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-7837083483172195919035790673586000000000000)
      constant := (37747415084981419019083444952855877319745911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186782923332295572483/100000000000000000000)
  centralHi := (46695730833073893121/25000000000000000000)
  directionLo := (19333869369735091289/10000000000000000000)
  directionHi := (193338693697350912891/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree016.table
  base := (3723557085578116650519343456685830206263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-743945727935626127671689781562952152000000000000)
      constant := (3622358857130447478913304442252511421136015379607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree016.table
  base := (3721083065965176833358732059017216632093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-16714397699411884760621604939412000000000000)
      constant := (81393337842157120184134762472051361519549237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19333869369735091289/10000000000000000000)
  centralHi := (193338693697350912891/100000000000000000000)
  directionLo := (99839672115644927943/50000000000000000000)
  directionHi := (199679344231289855887/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree017.table
  base := (2897292323041180834363218779505875622319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-790245592150030830466792838666531098250000000000)
      constant := (3924177513323173447514937844805181847957583634991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree017.table
  base := (2895141718425891691153820380399066366947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-17754628432479377683171628531652000000000000)
      constant := (88178294367607526223702019691244977424754123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99839672115644927943/50000000000000000000)
  centralHi := (199679344231289855887/100000000000000000000)
  directionLo := (205824756879919139839/100000000000000000000)
  directionHi := (40200147828109207/19531250000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree018.table
  base := (67844511794775194717823584059246220023/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-418272728182217766630947947885055022250000000000)
      constant := (2131477778450876154949826921535542105785752171952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree018.table
  base := (173532664885490205008073841040809955517/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-37589718331093741211443304247784000000000000)
      constant := (191587177212016564310722387601842879126181325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205824756879919139839/100000000000000000000)
  centralHi := (40200147828109207/19531250000000000)
  directionLo := (211791927553241965221/100000000000000000000)
  directionHi := (105895963776620982611/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree019.table
  base := (764364193285617200673372933312409139119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-441422660289420118028499476436844495375000000000)
      constant := (2318344463395218965282712228756893013394808300191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree019.table
  base := (3054224010138007974395457980527837841071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-39670179797228727056543351432264000000000000)
      constant := (208388436042203406531122586591878696495568439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211791927553241965221/100000000000000000000)
  centralHi := (105895963776620982611/50000000000000000000)
  directionLo := (13599720040885372511/6250000000000000000)
  directionHi := (217595520654165960177/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree020.table
  base := (38298953387638025197068414319026419543/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-929145184793244938852102009977267937000000000000)
      constant := (5043760539295088595361625157315032493263679838175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree020.table
  base := (1912151877491247420347075103482764870229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-41750641263363712901643398616744000000000000)
      constant := (226687742116849489331302839480563086520473261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13599720040885372511/6250000000000000000)
  centralHi := (217595520654165960177/100000000000000000000)
  directionLo := (223248293701872303493/100000000000000000000)
  directionHi := (111624146850936151747/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree021.table
  base := (44678510454493957093478796779528907659/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-487722524503824820823602533540423441625000000000)
      constant := (2741430159537916489185209290802037541922969881255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree021.table
  base := (27848616936903584051224743922492605553/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-10957775682374674686685861450306000000000000)
      constant := (61606565596352475904183343266842253831987016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223248293701872303493/100000000000000000000)
  centralHi := (111624146850936151747/50000000000000000000)
  directionLo := (22876142741475737839/10000000000000000000)
  directionHi := (228761427414757378391/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree022.table
  base := (-947866683103123700913694879942228697/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-2043489826444108688884616248368851659000000000000)
      constant := (11905847887281545277467090188567911652803301104175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree022.table
  base := (-5155841895501033399702105607631712993/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-45911564195633684591843492985704000000000000)
      constant := (267556202237930246894913862363668812591013315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22876142741475737839/10000000000000000000)
  centralHi := (228761427414757378391/100000000000000000000)
  directionLo := (117072392886706194303/50000000000000000000)
  directionHi := (234144785773412388607/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree023.table
  base := (-850709761748103132940383000839107430689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-2136089554872918094474822362576009551500000000000)
      constant := (12906169901324029551458868192585263456517555742079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree023.table
  base := (-213126008715077819373443876799144985087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-11998006415442167609235885042546000000000000)
      constant := (72509663513138773728873818892239201736890617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117072392886706194303/50000000000000000000)
  centralHi := (234144785773412388607/100000000000000000000)
  directionLo := (239407123404707931701/100000000000000000000)
  directionHi := (119703561702353965851/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree024.table
  base := (-799384214993102879781779375410094732279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-1114344641650863750032514238391583722000000000000)
      constant := (6982636794354360811785646958374056957839596454569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree024.table
  base := (-800156424555142961134563491403904892483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-25036243563951828141021793677332000000000000)
      constant := (156920946330205086126385371593094431157015253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239407123404707931701/100000000000000000000)
  centralHi := (119703561702353965851/50000000000000000000)
  directionLo := (244556252770107933243/100000000000000000000)
  directionHi := (61139063192526983311/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree025.table
  base := (-1138549711234688050289526934715439959247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-1160644505865268452827617295495162668250000000000)
      constant := (7541002528355382087285398066230564695044201855217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree025.table
  base := (-569606915824128047446806928636145359763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-13038237148509660531785908634786000000000000)
      constant := (84735003358100606127812161380861067684425733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244556252770107933243/100000000000000000000)
  centralHi := (61139063192526983311/25000000000000000000)
  directionLo := (124799590144556159929/50000000000000000000)
  directionHi := (249599180289112319859/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree026.table
  base := (-90413950366588057706999653986845484187/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-603472185039836577811360176299370807250000000000)
      constant := (4063855224374492853843345614173795638345554596456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree026.table
  base := (-2894387896528991931685564492161520564953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-54233410060173627972243681723624000000000000)
      constant := (365311838140251856489679282188302288733047023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124799590144556159929/50000000000000000000)
  centralHi := (249599180289112319859/100000000000000000000)
  directionLo := (127271109087094730807/50000000000000000000)
  directionHi := (50908443634837892323/20000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree027.table
  base := (-215836505904146663841881035112924114033/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-626622117147038929208911704851160280375000000000)
      constant := (4371187226664208663907985938319924862548177413452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree027.table
  base := (-1727182227365437105472656845141042608261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-28156935763154306908671864454052000000000000)
      constant := (196470016354610171235074264372222811313394851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127271109087094730807/50000000000000000000)
  centralHi := (50908443634837892323/20000000000000000000)
  directionLo := (64847769268243018961/25000000000000000000)
  directionHi := (51878215414594415169/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree028.table
  base := (-3962572132997778551023430524730759319451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-2599088197016965122425852933611799014000000000000)
      constant := (18769356325402875017088709277905904615177470179461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree028.table
  base := (-1981706820954923114748268335395900784323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-29197166496221799831221888046292000000000000)
      constant := (210905196990675144551217421413168914696836693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64847769268243018961/25000000000000000000)
  centralHi := (51878215414594415169/20000000000000000000)
  directionLo := (132075471698113207547/50000000000000000000)
  directionHi := (52830188679245283019/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree029.table
  base := (-4424960860729754239948109891965055407443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-2691687925445774528016059047818956906500000000000)
      constant := (20108724115161328515495733282342348913779116623373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree029.table
  base := (-2212841415710994258144843412458419993739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-30237397229289292753771911638532000000000000)
      constant := (225955635992442233090358200429012298237587149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132075471698113207547/50000000000000000000)
  centralHi := (52830188679245283019/20000000000000000000)
  directionLo := (268826544316509569223/100000000000000000000)
  directionHi := (33603318039563696153/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree030.table
  base := (-1210989544392791884301713689347413014067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-696071913468645983401566290506528699750000000000)
      constant := (5375606521427756434886623702899592568504456168237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree030.table
  base := (-60557216568131281355271247573413481613/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-15638813981178392838160967615386000000000000)
      constant := (120808275306497565217046977647405630602981660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268826544316509569223/100000000000000000000)
  centralHi := (33603318039563696153/12500000000000000000)
  directionLo := (273422202758291293843/100000000000000000000)
  directionHi := (68355550689572823461/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree031.table
  base := (-5222365141961576003820361098843487421911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-2876887382303393339196471276233272691500000000000)
      constant := (22950111938114856483273659308261075765803507936521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree031.table
  base := (-1044579182210848737069457527458312547017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-64635717390848557197743917646024000000000000)
      constant := (515768019911819348123061085946752000277146235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273422202758291293843/100000000000000000000)
  centralHi := (68355550689572823461/25000000000000000000)
  directionLo := (277941884201061044501/100000000000000000000)
  directionHi := (138970942100530522251/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree032.table
  base := (-5562486266793053847588332650540548133783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-2969487110732202744786677390440430584000000000000)
      constant := (24451493471168144034099716008978272404609194383113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree032.table
  base := (-1390735280321009359611693503850918877573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-16679044714245885760710991207626000000000000)
      constant := (137377390056757989855237149416674768872897443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277941884201061044501/100000000000000000000)
  centralHi := (138970942100530522251/50000000000000000000)
  directionLo := (70597309184413988407/25000000000000000000)
  directionHi := (282389236737655953629/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree033.table
  base := (-183319354451704969341274230564771243477/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-765521709790253037594220876161897119125000000000)
      constant := (6501583337043654049875975556801523099302380623976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree033.table
  base := (-5866609025380549754898020187913042983031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-68796640323118528887944012014984000000000000)
      constant := (584452396113131064003867833504664262260665921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70597309184413988407/25000000000000000000)
  centralHi := (282389236737655953629/100000000000000000000)
  directionLo := (2294141004312553001/800000000000000000)
  directionHi := (143383812769534562563/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree034.table
  base := (-6135128668615987619783780447327465780729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-3154686567589821555967089618854746369000000000000)
      constant := (27614435938616912904291246706411220333859545212519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree034.table
  base := (-6135462430132469692056724662596564311141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-70877101789253514733044059199464000000000000)
      constant := (620592137645847234309706636352302250850004931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2294141004312553001/800000000000000000)
  centralHi := (143383812769534562563/50000000000000000000)
  directionLo := (291080162651726650737/100000000000000000000)
  directionHi := (145540081325863325369/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree035.table
  base := (-6370504824160122125307779669690092567621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-3247286296018630961557295733061904261500000000000)
      constant := (29275639843359439181223782435912480413021244794331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree035.table
  base := (-1274158124405155072419830266343211104679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-72957563255388500578144106383944000000000000)
      constant := (657925163219441357821361880936249600034783445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291080162651726650737/100000000000000000000)
  centralHi := (145540081325863325369/50000000000000000000)
  directionLo := (14766486643866535731/5000000000000000000)
  directionHi := (295329732877330714621/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree036.table
  base := (-6573413501917745856576131849262748753259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-3339886024447440367147501847269062154000000000000)
      constant := (30989811787401346304697101637265201824432042375349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree036.table
  base := (-6573658176893446182202016973057955094487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-75038024721523486423244153568424000000000000)
      constant := (696448482440398595355984169827704204139586017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14766486643866535731/5000000000000000000)
  centralHi := (295329732877330714621/100000000000000000000)
  directionLo := (29951901634693478383/10000000000000000000)
  directionHi := (299519016346934783831/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree037.table
  base := (-1348947090161537468784198693986619883839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-3432485752876249772737707961476220046500000000000)
      constant := (32756841624732908276229243820326356439589901508645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree037.table
  base := (-3372472439803894594542320692260343991997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-38559243093829236134172100376452000000000000)
      constant := (368079811996506318223714466857184693726480427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29951901634693478383/10000000000000000000)
  centralHi := (299519016346934783831/100000000000000000000)
  directionLo := (303650508291152475223/100000000000000000000)
  directionHi := (37956313536394059403/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree038.table
  base := (-3361913661425844776048558951988476813/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-881271370326264794581978518920844484750000000000)
      constant := (8644159562136163354030627202848861549250095178816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree038.table
  base := (-3442689203450737554582009363831972737249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-39599473826896729056722123968692000000000000)
      constant := (388528271916670704512595417998211988581067559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303650508291152475223/100000000000000000000)
  centralHi := (37956313536394059403/12500000000000000000)
  directionLo := (307726536420756424077/100000000000000000000)
  directionHi := (153863268210378212039/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree039.table
  base := (-3497703877429509166967958761742687421179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-1808842604866934291959060094945267915750000000000)
      constant := (18224563119632541704632514047999230338878438982469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree039.table
  base := (-3497780556349057505373546755258674231717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-40639704559964221979272147560932000000000000)
      constant := (409568774974606744799197834775406384083106947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307726536420756424077/100000000000000000000)
  centralHi := (153863268210378212039/50000000000000000000)
  directionLo := (9742164883171171027/3125000000000000000)
  directionHi := (62349855252295494573/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree040.table
  base := (-7075860800645491751505539455766976437371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-3710284938162677989508326304097693724000000000000)
      constant := (38374243114539598485789211791289390908667342236581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree040.table
  base := (-7075992002337753069272795439398526730397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-83359870586063429803644342306344000000000000)
      constant := (862401240634628694078235480832489538414314827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9742164883171171027/3125000000000000000)
  centralHi := (62349855252295494573/20000000000000000000)
  directionLo := (12628830589193593177/4000000000000000000)
  directionHi := (157860382364919914713/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree041.table
  base := (-7126972547307447403082884024942080062879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-3802884666591487395098532418304851616500000000000)
      constant := (40351937070807502859519189168872473702754889391169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree041.table
  base := (-356354238890944577730051518931438689681/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-21360083013049603912186097372706000000000000)
      constant := (226711613450168307397168448567143943603430355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12628830589193593177/4000000000000000000)
  centralHi := (157860382364919914713/50000000000000000000)
  directionLo := (319642912190517287967/100000000000000000000)
  directionHi := (9988841005953665249/3125000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree042.table
  base := (-1787271670395349966959260947916996211783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-973871098755074200172184633128002377250000000000)
      constant := (10595541281695287984885755867129551431730107241113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree042.table
  base := (-3574591335541291185960878359085918593409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-43760396759166700746922218337652000000000000)
      constant := (476236112654412340664016008370831654671114119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319642912190517287967/100000000000000000000)
  centralHi := (9988841005953665249/3125000000000000000)
  directionLo := (40439689149722279923/12500000000000000000)
  directionHi := (64703502639555647877/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree043.table
  base := (-1785622140161111879801750555169966944283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-997021030862276551569736161679791850375000000000)
      constant := (11116222898959448830193926061361839056711232798613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree043.table
  base := (-3571285324392415318784365422804620346291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-44800627492234193669472241929892000000000000)
      constant := (499638877343873165462264313279517821447268581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40439689149722279923/12500000000000000000)
  centralHi := (64703502639555647877/20000000000000000000)
  directionLo := (65469251218481027971/20000000000000000000)
  directionHi := (20459141005775321241/6250000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree044.table
  base := (-3553707636274762916845806834559167064211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-2040341925938957805934575380463162647000000000000)
      constant := (23300043413933342443788156632335248802809142151821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree044.table
  base := (-444217841488231466652080514844446462993/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-22920429112650843296011132761066000000000000)
      constant := (261815594224645303963108465591751799541810652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65469251218481027971/20000000000000000000)
  centralHi := (20459141005775321241/6250000000000000000)
  directionLo := (16556536579985135963/5000000000000000000)
  directionHi := (331130731599702719261/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree045.table
  base := (-1761015982435415737617440792649300992571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-1043320895076681254364839218783370796625000000000)
      constant := (12196931543021542470067129571073534425509534193781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree045.table
  base := (-3522061970535384974755493483645020076471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-46881088958369179514572289114372000000000000)
      constant := (548212769530081987267570600768681138605192961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16556536579985135963/5000000000000000000)
  centralHi := (331130731599702719261/100000000000000000000)
  directionLo := (334872440552808455239/100000000000000000000)
  directionHi := (8371811013820211381/2500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree046.table
  base := (-6952598512140235919120949338356824102451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-4265883308735534423049562989340641079000000000000)
      constant := (51027789121251326743833579542870230111147094292461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree046.table
  base := (-869081226736898229145015268166778386987/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-23960659845718336218561156353306000000000000)
      constant := (286691695311390443120282548276255039021907034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334872440552808455239/100000000000000000000)
  centralHi := (8371811013820211381/2500000000000000000)
  directionLo := (338572800847667184051/100000000000000000000)
  directionHi := (84643200211916796013/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree047.table
  base := (-6833155518410110924666829199412059252393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-4358483037164343828639769103547798971500000000000)
      constant := (53320258604908878130919309158667036654723634392823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree047.table
  base := (-3416599684774959602667711026513957412939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-48961550424504165359672336298852000000000000)
      constant := (599142860311923657165668002663786293627054349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338572800847667184051/100000000000000000000)
  centralHi := (84643200211916796013/25000000000000000000)
  directionLo := (342233153721076498079/100000000000000000000)
  directionHi := (2138957210756728113/625000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree048.table
  base := (-835731079622597656195413553043085251377/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-1112770691398288308557493804438739216000000000000)
      constant := (13916280101310481599773209725872349629958711667294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree048.table
  base := (-835735764410064516044793119725963431769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-25000890578785829141111179945546000000000000)
      constant := (312745509588291965299174415482947537440321758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342233153721076498079/100000000000000000000)
  centralHi := (2138957210756728113/625000000000000000)
  directionLo := (345854769430629434459/100000000000000000000)
  directionHi := (17292738471531471723/5000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree049.table
  base := (-6510772610051727658096494174251328863501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-4543682494021962639820181331962114756500000000000)
      constant := (58062362673839417747907218765971329668025239189011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree049.table
  base := (-1627701159509412765948165612881373610647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-25521005945319575602386191741666000000000000)
      constant := (326213867184694742128670632129040221527692577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345854769430629434459/100000000000000000000)
  centralHi := (17292738471531471723/5000000000000000000)
  directionLo := (174719426202378623901/50000000000000000000)
  directionHi := (349438852404757247803/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree050.table
  base := (-630800643258725899788297704792230332819/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-2318141111225386022705193723084636324500000000000)
      constant := (30255987765815741069820669528952955361568029652545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree050.table
  base := (-1577008449947092983863444751511804234503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-26041121311853322063661203537786000000000000)
      constant := (339976447564353799666823283479803341905281073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174719426202378623901/50000000000000000000)
  centralHi := (349438852404757247803/100000000000000000000)
  directionLo := (88246636480517485509/25000000000000000000)
  directionHi := (352986545922069942037/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree051.table
  base := (-121552320056360878122728176066985959103/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-2364440975439790725500296780188215270750000000000)
      constant := (31506975368709533075198467053307374474305410540825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree051.table
  base := (-3038819692425182708304855337617051078741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-53122473356774137049872430667812000000000000)
      constant := (708066409060464084894659810522825703519816531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88246636480517485509/25000000000000000000)
  centralHi := (352986545922069942037/100000000000000000000)
  directionLo := (44562367046441472361/12500000000000000000)
  directionHi := (356498936371531778889/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree052.table
  base := (-1163931263989906880440461583922556604983/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-4821481679308390856590799674583588434000000000000)
      constant := (65568281413029640544620635256663983541286255831565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree052.table
  base := (-2909838147439425869462778284916977865517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-54162704089841629972422454260052000000000000)
      constant := (736768199055284184125007363246692209175762747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44562367046441472361/12500000000000000000)
  centralHi := (356498936371531778889/100000000000000000000)
  directionLo := (89994264284617514071/25000000000000000000)
  directionHi := (71995411427694011257/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree053.table
  base := (-5534173307756434744429463076332946537097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6767192)
      previous := (3383596)
      next := (3383596)
      square := (31207622956130628305154717217060000000000000)
      linear := (-1749405983530509171299752861798058500000000000)
      constant := (24270189325475047296773662873624538652846904463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree053.table
  base := (-2767095185061919534577973463476860263847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (76)
      previous := (38)
      next := (38)
      square := (350482052920314327004724930000000000000)
      linear := (-19652166188290894587031853988000000000000)
      constant := (272715628597556696530609593080523139736153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89994264284617514071/25000000000000000000)
  centralHi := (71995411427694011257/20000000000000000000)
  directionLo := (363421892155815521871/100000000000000000000)
  directionHi := (22713868259738470117/6250000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree054.table
  base := (-5221205328810705332275944972924826304967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-5006681136166009667771211902997904219000000000000)
      constant := (70833987146504721993162223174062068324449568818137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree054.table
  base := (-2610609950825957701076801515817824797719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-56243165555976615817522501444532000000000000)
      constant := (795936360306418791344314114627475730143207329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363421892155815521871/100000000000000000000)
  centralHi := (22713868259738470117/6250000000000000000)
  directionLo := (73366875831032379973/20000000000000000000)
  directionHi := (183417189577580949933/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree055.table
  base := (-4880784442675897094831623933404698786367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-5099280864594819073361418017205062111500000000000)
      constant := (73545353397412947711978193325018461325593647813537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree055.table
  base := (-2440398443909599738470250394186969629131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-57283396289044108740072525036772000000000000)
      constant := (826402632841239107725546301081688802311771021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73366875831032379973/20000000000000000000)
  centralHi := (183417189577580949933/50000000000000000000)
  directionLo := (185107706324043240269/50000000000000000000)
  directionHi := (370215412648086480539/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree056.table
  base := (-1128234363009671517811975333241625345577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-1297970148255907119737906032853055001000000000000)
      constant := (19077264304013446370130077803816214248002691969847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree056.table
  base := (-4512948078926399766870286255886613126583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-116647254044223203325245097258024000000000000)
      constant := (1714913961528400729294707420872718503727428353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185107706324043240269/50000000000000000000)
  centralHi := (370215412648086480539/100000000000000000000)
  directionLo := (186782923332295572483/50000000000000000000)
  directionHi := (373565846664591144967/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree057.table
  base := (-4117686773062486967071122692510741814911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-5284480321452437884541830245619377896500000000000)
      constant := (79125095799073293315217865408139999008131922759521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree057.table
  base := (-1029423961576599458806328137081437089721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-29681928877589547292586286110626000000000000)
      constant := (444549686327382764977053138871330243214973711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186782923332295572483/50000000000000000000)
  centralHi := (373565846664591144967/100000000000000000000)
  directionLo := (376886497272418470109/100000000000000000000)
  directionHi := (37688649727241847011/10000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree058.table
  base := (-230940697495733721937441262786430975721/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-1344270012470311822533009089956633947250000000000)
      constant := (20498366700270687141711558579451435148810866333724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree058.table
  base := (-461882363222904624397999073442179535097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-30202044244123293753861297906746000000000000)
      constant := (460664891113279867406222461025929835371825054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376886497272418470109/100000000000000000000)
  centralHi := (37688649727241847011/10000000000000000000)
  directionLo := (380178144898299705969/100000000000000000000)
  directionHi := (38017814489829970597/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree059.table
  base := (-324504630835976970531961553515699278209/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-2734839889155028347861121237016846840750000000000)
      constant := (42457084129592131605038009405516560436517880623995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree059.table
  base := (-3245052920249827554442076801972737723461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-122888638442628160860545238811464000000000000)
      constant := (1908296374962099773390421923774394579734798051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380178144898299705969/100000000000000000000)
  centralHi := (38017814489829970597/10000000000000000000)
  directionLo := (7668830729396820859/2000000000000000000)
  directionHi := (383441536469841042951/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree060.table
  base := (-1383842679277582368289197140616018210509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-2781139753369433050656224294120425787000000000000)
      constant := (43943599265035032981469369548332952290504050030099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree060.table
  base := (-11070764007349152324338234660257319533/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-62484549954381573352822642997972000000000000)
      constant := (987554570002247829573529023915237148678975375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7668830729396820859/2000000000000000000)
  centralHi := (383441536469841042951/100000000000000000000)
  directionLo := (386677387394701825781/100000000000000000000)
  directionHi := (193338693697350912891/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree061.table
  base := (-2262979314615996944508465855422587721349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-5654879235167675506902654702448009466500000000000)
      constant := (90912556237573274997744722677560984542401044669339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree061.table
  base := (-2262984130626323204735796879734010674513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-127049561374898132550745333180424000000000000)
      constant := (2043097828737260427590183392675451164015292983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386677387394701825781/100000000000000000000)
  centralHi := (193338693697350912891/50000000000000000000)
  directionLo := (194943191695960609579/50000000000000000000)
  directionHi := (389886383391921219159/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree062.table
  base := (-108183587150814203115866961686105347699/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-1436869740899121228123215204163791839750000000000)
      constant := (23497560057227920821426137567574873250282007936756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree062.table
  base := (-432735375986375190118160330702934584501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-32282505710258279598961345091226000000000000)
      constant := (528065603831274532917766771751327456752136691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194943191695960609579/50000000000000000000)
  centralHi := (389886383391921219159/100000000000000000000)
  directionLo := (393069182188672804773/100000000000000000000)
  directionHi := (196534591094336402387/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree063.table
  base := (-29289183040549446662752533920448134823/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-1460019673006323579520766732715581312875000000000)
      constant := (24280062384541587951260625783983284010271731395530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree063.table
  base := (-1171570827902545380649672151435677077681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-131210484307168104240945427549384000000000000)
      constant := (2182602878121552172897425115158649183088794071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393069182188672804773/100000000000000000000)
  centralHi := (196534591094336402387/50000000000000000000)
  directionLo := (396226415094339622641/100000000000000000000)
  directionHi := (198113207547169811321/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree064.table
  base := (-73109446197615862130768818315475964247/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-1483169605113525930918318261267370786000000000000)
      constant := (25075645838946232096002303299958447414238975820434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree064.table
  base := (-36554910050794237493403474140643254781/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-33322736443325772521511368683466000000000000)
      constant := (563529799746303752988922160905419732389280684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396226415094339622641/100000000000000000000)
  centralHi := (198113207547169811321/50000000000000000000)
  directionLo := (399358688462579711773/100000000000000000000)
  directionHi := (199679344231289855887/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree065.table
  base := (29132434991950652469800285137650373059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-6025278148882913129263479159276641036500000000000)
      constant := (103537241003104811109333221877150418420081042906851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree065.table
  base := (7282470862714275556936120367404901717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-33842851809859518982786380479586000000000000)
      constant := (581702840677129239197289711530952040368923053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399358688462579711773/100000000000000000000)
  centralHi := (199679344231289855887/50000000000000000000)
  directionLo := (80493317010194497173/20000000000000000000)
  directionHi := (201233292525486242933/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree066.table
  base := (335226070871582626117927282138643642693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-3058938938655861267426842636741899464500000000000)
      constant := (53412110955530558905525326855560796520139535163877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree066.table
  base := (134089993103280270901845934317158607259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-137451868705573061776245569102824000000000000)
      constant := (2400679356540362767346713297915228492638952655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80493317010194497173/20000000000000000000)
  centralHi := (201233292525486242933/50000000000000000000)
  directionLo := (405550665286880698853/100000000000000000000)
  directionHi := (202775332643440349427/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree067.table
  base := (1339079734339053150464737012485792596737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-6210477605740531940443891387690956821500000000000)
      constant := (110163525602385110646865169218727112422798537287393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree067.table
  base := (1339077878437989156060518623256542669473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-139532330171708047621345616287304000000000000)
      constant := (2475723169787041309963653445853335628358549657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405550665286880698853/100000000000000000000)
  centralHi := (202775332643440349427/50000000000000000000)
  directionLo := (81722293689463076233/20000000000000000000)
  directionHi := (204305734223657690583/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree068.table
  base := (50875300285291842317855011475505033127/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-1575769333542335336508524375474528678500000000000)
      constant := (28388787919178837714387473847195541404160406921030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree068.table
  base := (1017505214435943091270831201581019882657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-70806395818921516733222831735892000000000000)
      constant := (1275971396739225017461454186692217084850383513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81722293689463076233/20000000000000000000)
  centralHi := (204305734223657690583/50000000000000000000)
  directionLo := (411649513759838279679/100000000000000000000)
  directionHi := (40200147828109207/9765625000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree069.table
  base := (1379123143474751163880062385203668729839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-3197838531299075375812151808052636303250000000000)
      constant := (58499549899070304867308894716459992717349256892271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree069.table
  base := (689561234416133855070183980864229489497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-35923313275994504827886427664066000000000000)
      constant := (657334555022211650143268410734191620635997073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411649513759838279679/100000000000000000000)
  centralHi := (40200147828109207/9765625000000000)
  directionLo := (414665301430866237117/100000000000000000000)
  directionHi := (207332650715433118559/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree070.table
  base := (877195076732303001719263154878546259179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-1622069197756740039303627432578107624750000000000)
      constant := (30123842421193470450818841889129502766376412299531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree070.table
  base := (7017558313306361368618798166934940443/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-36443428642528251289161439460186000000000000)
      constant := (676977360825785456197643296791885030963048375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414665301430866237117/100000000000000000000)
  centralHi := (207332650715433118559/50000000000000000000)
  directionLo := (16706372544285777603/4000000000000000000)
  directionHi := (104414828401786110019/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree071.table
  base := (4286612179518381890984095511109297277/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-1645219129863942390701178961129897097875000000000)
      constant := (31010990275005892809938555653674154709531584113250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree071.table
  base := (214330559950653145867673729915829082081/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-36963544009061997750436451256306000000000000)
      constant := (696914114455311239845880960520883819457827645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16706372544285777603/4000000000000000000)
  centralHi := (104414828401786110019/25000000000000000000)
  directionLo := (210316007637810881799/50000000000000000000)
  directionHi := (420632015275621763599/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree072.table
  base := (636467539577812773904652040857995971989/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-1668369061971144742098730489681686571000000000000)
      constant := (31911218461320847541539005356185147048892005307242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree072.table
  base := (5091739480928059179403483071134988326469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-149934637502382976846845852209704000000000000)
      constant := (2868579259194216515013438980058946182209051421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210316007637810881799/50000000000000000000)
  centralHi := (420632015275621763599/100000000000000000000)
  directionLo := (423583855106483930443/100000000000000000000)
  directionHi := (105895963776620982611/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree073.table
  base := (5924163384918577559368056254866596559749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-6766075976313388373985128072933904176500000000000)
      constant := (131298107753808646112276945998763607331946992908261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree073.table
  base := (1481040668182516541943976134056329794487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-38003774742129490672986474848546000000000000)
      constant := (737669460921754697375770148377532230392713983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423583855106483930443/100000000000000000000)
  centralHi := (105895963776620982611/25000000000000000000)
  directionLo := (213257633121836136281/50000000000000000000)
  directionHi := (426515266243672272563/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree074.table
  base := (6783880264824700979549359150586502355921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-6858675704742197779575334187141062069000000000000)
      constant := (135003662685584997893072124771058559102491276384369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree074.table
  base := (678387965795906960021572423517653327953/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-77047780217326474268522973289332000000000000)
      constant := (1516976104081757801366797172990353440991099885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213257633121836136281/50000000000000000000)
  centralHi := (426515266243672272563/100000000000000000000)
  directionLo := (10735666676170794407/2500000000000000000)
  directionHi := (429426667046831776281/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree075.table
  base := (767089001611069765306113001234760010679/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-3475637716585503592582770150674109980750000000000)
      constant := (69380769261513870152916478656316639083186063915155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree075.table
  base := (7670889499051199740215306823902969447179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-156176021900787934382145993763144000000000000)
      constant := (3118402349990090044615130289789143441177125811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10735666676170794407/2500000000000000000)
  centralHi := (429426667046831776281/100000000000000000000)
  directionLo := (216159230894143396537/50000000000000000000)
  directionHi := (17292738471531471723/4000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree076.table
  base := (8585191849068026698961488381611918264583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-7043875161599816590755746415555377854000000000000)
      constant := (142571735167376326769053242214643920114728516778087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree076.table
  base := (8585191408574845793298769074438805005193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-158256483366922920227246040947624000000000000)
      constant := (3204028266954846720426005668948082603259587137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216159230894143396537/50000000000000000000)
  centralHi := (17292738471531471723/4000000000000000000)
  directionLo := (13599720040885372511/3125000000000000000)
  directionHi := (435191041308331920353/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree077.table
  base := (4763392550167390761425596822077992182337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-3568237445014312998172976264881267873250000000000)
      constant := (73217126267835528110985840091943825674664372545793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree077.table
  base := (4763392362556142126356454522426711654021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-80168472416528953036173044066052000000000000)
      constant := (1645414978599931622417875369601320633036144989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13599720040885372511/3125000000000000000)
  centralHi := (435191041308331920353/100000000000000000000)
  directionLo := (43804478363184526309/10000000000000000000)
  directionHi := (438044783631845263091/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree078.table
  base := (5247834606309907643627372707085268535007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-3614537309228717700968079321984846819500000000000)
      constant := (75174545279108691308434809546047931397947004031423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree078.table
  base := (10495668893032229932624899096858453790579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-162417406299192891917446135316584000000000000)
      constant := (3378807419164371337757361087716867396697736411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43804478363184526309/10000000000000000000)
  centralHi := (438044783631845263091/100000000000000000000)
  directionLo := (440880054548978211723/100000000000000000000)
  directionHi := (110220013637244552931/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree079.table
  base := (5745921858846841846857349590959290001713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-3660837173443122403763182379088425765750000000000)
      constant := (77158124588229385457514003720317495081549849404657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree079.table
  base := (35912010767256829709808194053463662323/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-41124466941331969440636545625266000000000000)
      constant := (866990162884273673550598630365798354197224560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440880054548978211723/100000000000000000000)
  centralHi := (110220013637244552931/25000000000000000000)
  directionLo := (110924302040611764277/25000000000000000000)
  directionHi := (443697208162447057109/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree080.table
  base := (12515308222117348102747740629013040658429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-7414274075315054213116570872384009424000000000000)
      constant := (158335728341191935991541806716821162859079354282781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree080.table
  base := (12515307990352545972320880176260319183907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-166578329231462863607646229685544000000000000)
      constant := (3558289653216260353714802687626635236587594763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110924302040611764277/25000000000000000000)
  centralHi := (443697208162447057109/100000000000000000000)
  directionLo := (223248293701872303493/50000000000000000000)
  directionHi := (446496587403744606987/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree081.table
  base := (13566062395265825892802963542349468693561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-7506873803743863618706776986591167316500000000000)
      constant := (162407528011069086469125980202156613220503861250329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree081.table
  base := (13566062197930512514476315347396951775621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-168658790697597849452746276870024000000000000)
      constant := (3649794423276042144426915325621942037537719389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223248293701872303493/50000000000000000000)
  centralHi := (446496587403744606987/100000000000000000000)
  directionLo := (89855704904080435149/20000000000000000000)
  directionHi := (224639262260201087873/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree082.table
  base := (2928821191855208661057809625904033279551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-7599473532172673024296983100798325209000000000000)
      constant := (166531648151340808331561788083567248491960711047195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree082.table
  base := (3661026447818453430526534643929452304171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-42684813040933208824461581013626000000000000)
      constant := (935618740234599216485958084262589831522416339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89855704904080435149/20000000000000000000)
  centralHi := (224639262260201087873/50000000000000000000)
  directionLo := (226021670768130932181/50000000000000000000)
  directionHi := (452043341536261864363/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree083.table
  base := (7874719340304196370745202323443518194831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-3846036630300741214943594607502741550750000000000)
      constant := (85354044366400378795646670825690023607003079801359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree083.table
  base := (3149887707518874366011923352212084958759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-172819713629867821142946371238984000000000000)
      constant := (3836331265549422807823245312633530733245770155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226021670768130932181/50000000000000000000)
  centralHi := (452043341536261864363/100000000000000000000)
  directionLo := (227395675343282068959/50000000000000000000)
  directionHi := (454791350686564137919/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree084.table
  base := (16882060362961879722018428382325504035453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-7784672989030291835477395329212640994000000000000)
      constant := (174936849730899632188536480967873717978591190063517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree084.table
  base := (16882060241232343319631550346273307347243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-174900175096002806988046418423464000000000000)
      constant := (3931363336559511469621111346815417720338405587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227395675343282068959/50000000000000000000)
  centralHi := (454791350686564137919/100000000000000000000)
  directionLo := (22876142741475737839/5000000000000000000)
  directionHi := (457522854829514756781/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree085.table
  base := (4510492710331223603139232773872001083717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-1969318179364775310266900360854949721625000000000)
      constant := (44804482781250291129586062216820646281097250490613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree085.table
  base := (18041970737723034440517572439081472632341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-176980636562137792833146465607944000000000000)
      constant := (4027571173506681526592825472995619856624245869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22876142741475737839/5000000000000000000)
  centralHi := (457522854829514756781/100000000000000000000)
  directionLo := (460238147835866715699/100000000000000000000)
  directionHi := (4602381478358667157/1000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree086.table
  base := (19229169976978916255225170465355370116667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-7969872445887910646657807557626956779000000000000)
      constant := (183551332897757287284912084791999317645758745403163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree086.table
  base := (3845833977762879735723320999395448427087/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-179061098028272778678246512792424000000000000)
      constant := (4124954776002582980080277762952733073158436915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460238147835866715699/100000000000000000000)
  centralHi := (4602381478358667157/1000000000000000000)
  directionLo := (462937514957935741373/100000000000000000000)
  directionHi := (231468757478967870687/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree087.table
  base := (4088731530660397809658376994249242944759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-8062472174316720052248013671834114671500000000000)
      constant := (187937055034583318239471096260922138395557703840755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree087.table
  base := (10221828789141147238707063689997601251657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-90570779747203882261673279988452000000000000)
      constant := (2111757071860371108225609464104547261915904513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462937514957935741373/100000000000000000000)
  centralHi := (231468757478967870687/50000000000000000000)
  directionLo := (116405308294840244939/25000000000000000000)
  directionHi := (465621233179360979757/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree088.table
  base := (4337086754448706191570474725514975856261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-8155071902745529457838219786041272564000000000000)
      constant := (192375097523217101721720478494095908509156690553145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree088.table
  base := (21685433708415359415135251774335886957947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-183222020960542750368446607161384000000000000)
      constant := (4323249276386688018662883308895741506464873123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116405308294840244939/25000000000000000000)
  centralHi := (465621233179360979757/100000000000000000000)
  directionLo := (117072392886706194303/25000000000000000000)
  directionHi := (468289571546824777213/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree089.table
  base := (5738624562840689049170292609160763613033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-2061917907793584715857106475062107614125000000000)
      constant := (49216365088337158797087837996515400561174606970137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree089.table
  base := (5738624549265506782945087202779340114397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-46325620606669434053386663586466000000000000)
      constant := (1106040043442414159202507986528871166381341173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117072392886706194303/25000000000000000000)
  centralHi := (468289571546824777213/100000000000000000000)
  directionLo := (58867848935607004887/12500000000000000000)
  directionHi := (470942791484856039097/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree090.table
  base := (24250851021340339094269822207168378740943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-8340271359603148269018632014455588349000000000000)
      constant := (201408143516308879193185347210537028218863294958127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree090.table
  base := (24250850975149531199319009046692352024321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-187382943892812722058646701530344000000000000)
      constant := (4526246835675622669996327419741118816836317689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58867848935607004887/12500000000000000000)
  centralHi := (470942791484856039097/100000000000000000000)
  directionLo := (236790573547379872069/50000000000000000000)
  directionHi := (473581147094759744139/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree091.table
  base := (25574492023887495267822519047889909806741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-8432871088031957674608838128662746241500000000000)
      constant := (206003147004808268146878839791179947416827743215349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree091.table
  base := (25574491984599253223318902844038603527111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-189463405358947707903746748714824000000000000)
      constant := (4629509261941443279151809315822248437307654799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236790573547379872069/50000000000000000000)
  centralHi := (473581147094759744139/100000000000000000000)
  directionLo := (476204885438640095317/100000000000000000000)
  directionHi := (238102442719320047659/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree092.table
  base := (26925421209988846564079129929860582149877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-8525470816460767080199044242869904134000000000000)
      constant := (210650470812716963904443354057437195619156139032853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree092.table
  base := (26925421176574937986052891798077312482793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-191543866825082693748846795899304000000000000)
      constant := (4733947452429937423369882102579007170764165537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476204885438640095317/100000000000000000000)
  centralHi := (238102442719320047659/50000000000000000000)
  directionLo := (478814246809415863403/100000000000000000000)
  directionHi := (119703561702353965851/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree093.table
  base := (28303638538425659097057497267287357699439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-8618070544889576485789250357077062026500000000000)
      constant := (215350114934880172668870977118512021824942681926671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree093.table
  base := (2830363851001049847091458881312016284449/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-96812164145608839796973421541892000000000000)
      constant := (2419780703512875232110449219329803268715086205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478814246809415863403/100000000000000000000)
  centralHi := (119703561702353965851/25000000000000000000)
  directionLo := (481409464987663159227/100000000000000000000)
  directionHi := (120352366246915789807/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree094.table
  base := (29709143974534617014117573610437239738909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-8710670273318385891379456471284219919000000000000)
      constant := (220102079366962917872584945339405064278380952957501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree094.table
  base := (237673151602981500438564321777757327309/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-195704789757352665439046890268264000000000000)
      constant := (4946351125631878510536116902713591041551372625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481409464987663159227/100000000000000000000)
  centralHi := (120352366246915789807/25000000000000000000)
  directionLo := (483990767486062644013/100000000000000000000)
  directionHi := (241995383743031322007/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree095.table
  base := (15570968744582243084239357615336643350731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-4401635000873597648484831292745688905750000000000)
      constant := (112453182052659780534734760210160966200300479136459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree095.table
  base := (1557096873431054406805421551104670059703/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-49446312805871912821036734363186000000000000)
      constant := (1263579152041686757669242012974185090988528635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483990767486062644013/100000000000000000000)
  centralHi := (241995383743031322007/50000000000000000000)
  directionLo := (486558375782174594401/100000000000000000000)
  directionHi := (243279187891087297201/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree096.table
  base := (407525238222488194098143596429531059039/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-2223967432544001175639967174924633926000000000000)
      constant := (57440742286721029358902605798348666711060923421420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree096.table
  base := (16301009520166946472757867830403288375029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-99932856344811318564623492318612000000000000)
      constant := (2581728927280877584012046725966834837045456461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486558375782174594401/100000000000000000000)
  centralHi := (243279187891087297201/50000000000000000000)
  directionLo := (489112505540215866487/100000000000000000000)
  directionHi := (61139063192526983311/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree097.table
  base := (34089388659819807260743088996412392458279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-8988469458604814108150074813905693596500000000000)
      constant := (234671894489078045667063775725184662156865450559431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree097.table
  base := (6817877728994599255449079277101783621771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-201946174155757622974347031821704000000000000)
      constant := (5273774864759211383649909167596622550967773695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489112505540215866487/100000000000000000000)
  centralHi := (61139063192526983311/12500000000000000000)
  directionLo := (98330673364493455711/20000000000000000000)
  directionHi := (122913341705616819639/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree098.table
  base := (8901011569471503965353059438201293597089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-2270267296758405878435070232028212872250000000000)
      constant := (59908285032433180873298076701776251100406547227521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree098.table
  base := (35604046265266158927992873086421721798729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-204026635621892608819447079006184000000000000)
      constant := (5385267638710597957632332745717230616532629761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98330673364493455711/20000000000000000000)
  centralHi := (122913341705616819639/25000000000000000000)
  directionLo := (9883623285817958377/2000000000000000000)
  directionHi := (494181164290897918851/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree099.table
  base := (18572995948706771874249076378421802419327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-4586834457731216459665243521160004690750000000000)
      constant := (122323353033512133060282670607152072688965310843903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree099.table
  base := (9286497971671891459630564924229814010297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-51526774272006898666136781547666000000000000)
      constant := (1374484044093777968867492631538585547554924273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9883623285817958377/2000000000000000000)
  centralHi := (494181164290897918851/100000000000000000000)
  directionLo := (49669609739955407889/10000000000000000000)
  directionHi := (496696097399554078891/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree100.table
  base := (19357612753068297762705247348359428882197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-4633134321945621162460346578263583637000000000000)
      constant := (124856296149709359722353369385055330817464398017333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree100.table
  base := (9678806374255270775721570461226038889641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-52046889638540645127411793343786000000000000)
      constant := (1402945119429609504255254153799183943241001569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49669609739955407889/10000000000000000000)
  centralHi := (496696097399554078891/100000000000000000000)
  directionLo := (499198360578224639717/100000000000000000000)
  directionHi := (249599180289112319859/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree101.table
  base := (629871048339675120481205201569880664353/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-2339717093080012932627724817683581291625000000000)
      constant := (63707699706406493586023985245907046924584623379872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree101.table
  base := (5038968385749128643436607049496427291211/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-52567005005074391588686805139906000000000000)
      constant := (1431700135677929402686312712829966928522023398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499198360578224639717/100000000000000000000)
  centralHi := (249599180289112319859/50000000000000000000)
  directionLo := (100337628681572309897/20000000000000000000)
  directionHi := (250844071703930774743/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree102.table
  base := (41935556651545362497998819449293445453611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-9451468100748861136101105384941483059000000000000)
      constant := (260001325644561012465277241513005947234040464864779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree102.table
  base := (4193555664496338109041114359502731762779/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-106174240743216276099923633872052000000000000)
      constant := (2921498185665340416183664752825839867608231055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100337628681572309897/20000000000000000000)
  centralHi := (250844071703930774743/50000000000000000000)
  directionLo := (504165630788203300481/100000000000000000000)
  directionHi := (252082815394101650241/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree103.table
  base := (43586654172258387753582722266635111581829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-9544067829177670541691311499148640951500000000000)
      constant := (265224172755311315719842990562928164164397141425381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree103.table
  base := (8717330833333221240983491466070093081191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-214428942952567538044947314928584000000000000)
      constant := (5960367963554917395957885743904346457325327595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504165630788203300481/100000000000000000000)
  centralHi := (252082815394101650241/50000000000000000000)
  directionLo := (253315501549010418813/50000000000000000000)
  directionHi := (506631003098020837627/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree104.table
  base := (4420414028295097199857720813667798643/976562500000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-2409166889401619986820379403338949711000000000000)
      constant := (67624835039277364508843462605741977747214091973120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree104.table
  base := (45265039644990794223684546678927056727647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-216509404418702523890047362113064000000000000)
      constant := (6078915319367263159075997318235122102347960423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253315501549010418813/50000000000000000000)
  centralHi := (506631003098020837627/100000000000000000000)
  directionLo := (127271109087094730807/25000000000000000000)
  directionHi := (509084436348378923229/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree105.table
  base := (46970713078834961360013804495585289076709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-9729267286035289352871723727562956736500000000000)
      constant := (275826827849310054429408946046064629443866134341701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree105.table
  base := (469707130747990143800663602599743886511/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-54647466471209377433786852324386000000000000)
      constant := (1549659609688321067424538867578847014430234975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127271109087094730807/25000000000000000000)
  centralHi := (509084436348378923229/100000000000000000000)
  directionLo := (511526102329281475401/100000000000000000000)
  directionHi := (255763051164640737701/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree106.table
  base := (2435183722759905194234501321583065743921/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1691798)
      previous := (845899)
      next := (845899)
      square := (7801905739032657076288679304265000000000000)
      linear := (-874142667716633922967419886237995250000000000)
      constant := (25027290479830043964622248995260595865550534205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree106.table
  base := (12175918612942467428426748697415994767457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (175241026460157163502362465000000000000)
      linear := (-19639580575914248449648225034000000000000)
      constant := (562436571885087515865318660361415994767457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511526102329281475401/100000000000000000000)
  centralHi := (255763051164640737701/50000000000000000000)
  directionLo := (51395616875004663679/10000000000000000000)
  directionHi := (513956168750046636791/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree107.table
  base := (50463923775181896584843665527001641167859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-9914466742892908164052135955977272521500000000000)
      constant := (286638764102834033822394577393724692356254434764051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree107.table
  base := (12615980943067525563371198533177979653877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-55687697204276870356336875916626000000000000)
      constant := (1610402992049933628282202894666888944847740493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51395616875004663679/10000000000000000000)
  centralHi := (513956168750046636791/100000000000000000000)
  directionLo := (64546849921717022033/12500000000000000000)
  directionHi := (103274959874747235253/20000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree108.table
  base := (52251461035717800165127945788077151595377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-10007066471321717569642342070184430414000000000000)
      constant := (292123212663317283980853421211446322479343382382353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree108.table
  base := (52251461033244843070430766122022640512737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-224831250283242467270447550850984000000000000)
      constant := (6564862378241376697474954903858073597200278233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64546849921717022033/12500000000000000000)
  centralHi := (103274959874747235253/20000000000000000000)
  directionLo := (518782154145944151689/100000000000000000000)
  directionHi := (51878215414594415169/10000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree109.table
  base := (54066286234225816787737143843464319043603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-10099666199750526975232548184391588306500000000000)
      constant := (297659981512497471250655032517807362010716584898867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree109.table
  base := (13516571558031430847937347982367670923203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-56727927937344363278886899508866000000000000)
      constant := (1672322137954638833354591957751054787623277227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518782154145944151689/100000000000000000000)
  centralHi := (51878215414594415169/10000000000000000000)
  directionLo := (32573649332389465663/6250000000000000000)
  directionHi := (521178389318231450609/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree110.table
  base := (27954199684268448774116120786051796461657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-5096132964089668190411377149299373099500000000000)
      constant := (151624535325051667742097128937463181707558082513273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree110.table
  base := (6988549920844198236501756407896277260777/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-57248043303878109740161911304986000000000000)
      constant := (1703722622231301337007981745926521285651045186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32573649332389465663/6250000000000000000)
  centralHi := (521178389318231450609/100000000000000000000)
  directionLo := (20942546302659030863/4000000000000000000)
  directionHi := (65445457195809471447/12500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree111.table
  base := (57777800436827673827085338387376878324947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-10284865656608145786412960412805904091500000000000)
      constant := (308890480075906847133654302614198067504998672772083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree111.table
  base := (2311112017412538992101194475238116957187/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-231072634681647424805747692404424000000000000)
      constant := (6941668189556228530561368437745420763318457075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20942546302659030863/4000000000000000000)
  centralHi := (65445457195809471447/12500000000000000000)
  directionLo := (105187621620878143001/20000000000000000000)
  directionHi := (262969054052195357503/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree112.table
  base := (11934897887513110790881662035844262081461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-10377465385036955192003166527013061984000000000000)
      constant := (314584209789716341067953301247249432645447945167145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree112.table
  base := (59674489436279952932976107130789832962453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-233153096147782410650847739588904000000000000)
      constant := (7069621653707339927939081300046676640791530477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105187621620878143001/20000000000000000000)
  centralHi := (262969054052195357503/50000000000000000000)
  directionLo := (132075471698113207547/25000000000000000000)
  directionHi := (528301886792452830189/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree113.table
  base := (15399616592365634544645881428490640020623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-2617516278366441149398343160305054969125000000000)
      constant := (80082564947842685174080456472151676912078468091647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree113.table
  base := (61598466368371104273320612059456908087013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-235233557613917396495947786773384000000000000)
      constant := (7198750881374938638092885191166246454816419517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132075471698113207547/25000000000000000000)
  centralHi := (528301886792452830189/100000000000000000000)
  directionLo := (106131027248492326647/20000000000000000000)
  directionHi := (132663784060615408309/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree114.table
  base := (6354973123143636686036877245010220747007/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-5281332420947287001591789377713688884500000000000)
      constant := (163064315040367349590655460545300354414520718497115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree114.table
  base := (6354973123050984193893865890499294668789/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-118657009540026191170523916978932000000000000)
      constant := (3664527936277999561981934639455390593623141505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106131027248492326647/20000000000000000000)
  centralHi := (132663784060615408309/25000000000000000000)
  directionLo := (26649899795897234753/5000000000000000000)
  directionHi := (532997995917944695061/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree115.table
  base := (65528284022577837039391210565663798305819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-10655264570323383408773784869634535661500000000000)
      constant := (331979320657694512065299072255616209847315414866491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree115.table
  base := (13105656804358272146767864857403046405041/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-239394480546187368186147881142344000000000000)
      constant := (7460536627247979787756495059504785786758800845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26649899795897234753/5000000000000000000)
  centralHi := (532997995917944695061/100000000000000000000)
  directionLo := (6691632527882597883/1250000000000000000)
  directionHi := (535330602230607830641/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree116.table
  base := (67534124742123307690777859205167101784859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-10747864298752192814363990983841693554000000000000)
      constant := (337882331522154678791936228107960070189075454477051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree116.table
  base := (2110441398170492442781964944550059764263/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-60368735503080588507811982081706000000000000)
      constant := (1898298286362186515844790572858664943022518136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6691632527882597883/1250000000000000000)
  centralHi := (535330602230607830641/100000000000000000000)
  directionLo := (537653088633019138447/100000000000000000000)
  directionHi := (33603318039563696153/6250000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree117.table
  base := (69567253389431569694109399697889156742459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-10840464027181002219954197098048851446500000000000)
      constant := (343837662674035010076280609188943517070493452143451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree117.table
  base := (13913450677773000591619226900241166447743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-243555403478457339876347975511304000000000000)
      constant := (7727025427156505720948392514609695182758550435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537653088633019138447/100000000000000000000)
  centralHi := (33603318039563696153/6250000000000000000)
  directionLo := (269982792853852542213/50000000000000000000)
  directionHi := (539965585707705084427/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree118.table
  base := (286510679855857549881937305706327990699/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-5466531877804905812772201606128004669500000000000)
      constant := (174922657056634097225936587012371445169682961601375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree118.table
  base := (8953458745435445062856208056444996048091/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-61408966236148081430362005673946000000000000)
      constant := (1965508368092438610944453860979395987798175238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269982792853852542213/50000000000000000000)
  centralHi := (539965585707705084427/100000000000000000000)
  directionLo := (271134110626413472843/50000000000000000000)
  directionHi := (542268221252826945687/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree119.table
  base := (14743074893054025870433152829660790311007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-11025663484038621031134609326463167231500000000000)
      constant := (355905285839797751093130531211019153510169057477115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree119.table
  base := (73715374464862094612312740933564456170229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-247716326410727311566548069880264000000000000)
      constant := (7998217281087230046506994306813358557382173261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271134110626413472843/50000000000000000000)
  centralHi := (542268221252826945687/100000000000000000000)
  directionLo := (544561120364596676391/100000000000000000000)
  directionHi := (68070140045574584549/12500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree120.table
  base := (7583036689296999634931367300159419838239/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-5559131606233715218362407720335162562000000000000)
      constant := (181008788926788153795974784585479192820033159999355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree120.table
  base := (4739397930788984811035690157585225266943/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-62449196969215574352912029266186000000000000)
      constant := (2033894213326968490558344943602947591099371548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544561120364596676391/100000000000000000000)
  centralHi := (68070140045574584549/12500000000000000000)
  directionLo := (546844405516582587687/100000000000000000000)
  directionHi := (68355550689572823461/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree121.table
  base := (9746580905843304607122933774941514813949/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-2802715735224059960578755388719370754125000000000)
      constant := (92045547538641037776721197126977524538165690274122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree121.table
  base := (311890588985810614082052842935374457113/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-125938624671498641628374082124612000000000000)
      constant := (4137056094515399422249992020369715356253802125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546844405516582587687/100000000000000000000)
  centralHi := (68355550689572823461/12500000000000000000)
  directionLo := (549118196636047103689/100000000000000000000)
  directionHi := (54911819663604710369/10000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree122.table
  base := (80142215526333400345795715470151400442631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-11303462669325049247905227669084640909000000000000)
      constant := (374399122742728009494683816934356163106552306675559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree122.table
  base := (20035553881521035507150706427396707889443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-63489427702283067275462052858426000000000000)
      constant := (2103455822063815328330841325601389352461445387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549118196636047103689/100000000000000000000)
  centralHi := (54911819663604710369/10000000000000000000)
  directionLo := (8615353299647675447/1562500000000000000)
  directionHi := (551382611177451228609/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree123.table
  base := (658712573852065105367528162268650264181/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-11396062397753858653495433783291798801500000000000)
      constant := (380668375618040025923651349818348481875914482938625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree123.table
  base := (41169535865648335161649362001883067602487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-128019086137633627473474129309092000000000000)
      constant := (4277355075490319514318405215646825536895385983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8615353299647675447/1562500000000000000)
  centralHi := (551382611177451228609/100000000000000000000)
  directionLo := (276818882096626600577/50000000000000000000)
  directionHi := (110727552838650640231/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree124.table
  base := (21140803965521076493047319556982828590457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-2872165531545667014771409974374739173500000000000)
      constant := (96747487195119224065829744532400102755859642696473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree124.table
  base := (84563215861904910447502506865099395308961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-258118633741402240792048305802664000000000000)
      constant := (8696772777206411404208830025311360201422871449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276818882096626600577/50000000000000000000)
  centralHi := (110727552838650640231/20000000000000000000)
  directionLo := (277941884201061044501/50000000000000000000)
  directionHi := (555883768402122089003/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree125.table
  base := (86814647917906161114332132032873259433743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-11581261854611477464675846011706114586500000000000)
      constant := (393363842230019143419312031299355266614438953937327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree125.table
  base := (43407323958876991566536619659314547002127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-130099547603768613318574176493572000000000000)
      constant := (4420005583466071692087608099057014562528974743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277941884201061044501/50000000000000000000)
  centralHi := (555883768402122089003/100000000000000000000)
  directionLo := (139530183563670189683/25000000000000000000)
  directionHi := (558120734254680758733/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree126.table
  base := (89093367898843681403380752107114110899917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-11673861583040286870266052125913272479000000000000)
      constant := (399790055966650506882491607427217866301895450162413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree126.table
  base := (89093367898714599499694482942644165086707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-262279556673672212482248400171624000000000000)
      constant := (8984425320157471796071160074175071459728559963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139530183563670189683/25000000000000000000)
  centralHi := (558120734254680758733/100000000000000000000)
  directionLo := (560348769996886717449/100000000000000000000)
  directionHi := (11206975399937734349/2000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree127.table
  base := (91399375804788458892957820110053964315797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-11766461311469096275856258240120430371500000000000)
      constant := (406268589990357429210480219680322458082523432447733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree127.table
  base := (91399375804678974402140329472590402480369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-264360018139807198327348447356104000000000000)
      constant := (9130015236882093871423722077179354440567356521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560348769996886717449/100000000000000000000)
  centralHi := (11206975399937734349/2000000000000000000)
  directionLo := (140641995432788434019/25000000000000000000)
  directionHi := (562567981731153736077/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree128.table
  base := (93732671635650245795160399681365171490829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-11859061039897905681446464354327588264000000000000)
      constant := (412799444301128624061039346455846946401040442926381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree128.table
  base := (18746534327111477790813441898422260700897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-266440479605942184172448494540584000000000000)
      constant := (9276780917105757589881163120636332651544098365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140641995432788434019/25000000000000000000)
  centralHi := (562567981731153736077/100000000000000000000)
  directionLo := (564778473475311907257/100000000000000000000)
  directionHi := (282389236737655953629/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree129.table
  base := (96093255391354049026585834127021120994777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-11951660768326715087036670468534746156500000000000)
      constant := (419382618898954712837480117126393933879579608288953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree129.table
  base := (48046627695637649598206921446559973087261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-134260470536038585008774270862532000000000000)
      constant := (4712361180414126778731240034361194964402116149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564778473475311907257/100000000000000000000)
  centralHi := (282389236737655953629/50000000000000000000)
  directionLo := (566980347219498841269/100000000000000000000)
  directionHi := (56698034721949884127/10000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree130.table
  base := (2462028176795942158459776579156826221079/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-3011065124188881123156719145685476012250000000000)
      constant := (106504528445956979764884336933014195889215032686310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree130.table
  base := (98481127071770904231545708841832961396393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-270601402538212155862648588909544000000000000)
      constant := (9573839568049408175446217552415428788562467937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (566980347219498841269/100000000000000000000)
  centralHi := (56698034721949884127/10000000000000000000)
  directionLo := (56917370298107004099/10000000000000000000)
  directionHi := (569173702981070040991/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree131.table
  base := (10089628667704973079133350011178966717393/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-6068430112592166949108541348474530970750000000000)
      constant := (216352964477870905650234263167339820899571192460885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree131.table
  base := (100896286676993100900895631145871697477211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-272681864004347141707748636094024000000000000)
      constant := (9724132538769077895059960373791057598213485699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56917370298107004099/10000000000000000000)
  centralHi := (569173702981070040991/100000000000000000000)
  directionLo := (285679319428806051573/50000000000000000000)
  directionHi := (571358638857612103147/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree132.table
  base := (103338734206947781956619449690132783150947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-12229459953613143303807288811156219834000000000000)
      constant := (439446064414691086984315332516944612937255241686083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree132.table
  base := (51669367103449881828250651040648938383491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-137381162735241063776424341639252000000000000)
      constant := (4937800636493572192819741205226366867919226219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285679319428806051573/50000000000000000000)
  centralHi := (571358638857612103147/100000000000000000000)
  directionLo := (573535251078138250251/100000000000000000000)
  directionHi := (143383812769534562563/25000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree133.table
  base := (3306514676921781624974351206119208563067/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-3080514920510488177349373731340844431625000000000)
      constant := (111559630040167847639955244163967615366887822592104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree133.table
  base := (105808469661456298012421378475669223151921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-276842786936617113397948730462984000000000000)
      constant := (10028245770703510471273774429429066847833746089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573535251078138250251/100000000000000000000)
  centralHi := (143383812769534562563/25000000000000000000)
  directionLo := (287851817026270894959/50000000000000000000)
  directionHi := (575703634052541789919/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree134.table
  base := (108305493040668943024493190880775418124077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-12414659410470762114987701039570535619000000000000)
      constant := (453083296193679160596049032176947223046920908216653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree134.table
  base := (108305493040634424152282230669788369143711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-278923248402752099243048777647464000000000000)
      constant := (10182066031918096713958642905007371528924684199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287851817026270894959/50000000000000000000)
  centralHi := (575703634052541789919/100000000000000000000)
  directionLo := (577863880419379410297/100000000000000000000)
  directionHi := (288931940209689705149/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree135.table
  base := (55414902172220209494792955246872804835689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-6253629569449785760288953576888846755750000000000)
      constant := (229990196256855750605048867005215263992505807802921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree135.table
  base := (110829804344411154159558784260459197683539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-281003709868887085088148824831944000000000000)
      constant := (10337062056630838540636568903189069886293061051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577863880419379410297/100000000000000000000)
  centralHi := (288931940209689705149/50000000000000000000)
  directionLo := (36251005068253296167/6250000000000000000)
  directionHi := (580016081092052738673/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree136.table
  base := (56690701786396370650221252902927118924139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-6299929433664190463084056633992425702000000000000)
      constant := (233464904560383036982677280675411695011395053104971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree136.table
  base := (56690701786383966067012447678894148701471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-141542085667511035466624436008212000000000000)
      constant := (5246616922420841913891908592893725663702432039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36251005068253296167/6250000000000000000)
  centralHi := (580016081092052738673/100000000000000000000)
  directionLo := (291080162651726650737/50000000000000000000)
  directionHi := (23286413012138132059/4000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree137.table
  base := (23192058145142188423226332651611146243111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-12692458595757190331758319382192009296500000000000)
      constant := (473931546014841006991281210840332798668354282151395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree137.table
  base := (2319205814513798226694605284764398457477/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-142582316400578528389174459600452000000000000)
      constant := (5325290698275295435452529180439523881676322325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291080162651726650737/50000000000000000000)
  centralHi := (23286413012138132059/4000000000000000000)
  directionLo := (116859340129826583263/20000000000000000000)
  directionHi := (146074175162283229079/25000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree138.table
  base := (118566465803183173500926802501325425485103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-12785058324185999737348525496399167189000000000000)
      constant := (480985603195934818591090011496792287757437058292367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree138.table
  base := (59283232901582673296451835749430155880633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-143622547133646021311724483192692000000000000)
      constant := (5404552355878763338910607036580565307868698097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116859340129826583263/20000000000000000000)
  centralHi := (146074175162283229079/25000000000000000000)
  directionLo := (146606323282264652203/25000000000000000000)
  directionHi := (586425293129058608813/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree139.table
  base := (30299982201300048508250832236934141912659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-3219414513153702285734682902651581270375000000000)
      constant := (122022995166011588259322486518350892997410773421251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree139.table
  base := (121199928805185083690184475328069941434987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-289325555733427028468549013569864000000000000)
      constant := (10968803790462465534332909279784804465490878483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146606323282264652203/25000000000000000000)
  centralHi := (586425293129058608813/100000000000000000000)
  directionLo := (73568273398501046061/12500000000000000000)
  directionHi := (588546187188008368489/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree140.table
  base := (123860679731754937395586251556778477397563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-12970257781043618548528937724813482974000000000000)
      constant := (495250678419174726619916022062660807385787278625307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree140.table
  base := (123860679731742130301876727716683575327427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-291406017199562014313649060754344000000000000)
      constant := (11129678632665387799000073062792324163094742443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73568273398501046061/12500000000000000000)
  centralHi := (588546187188008368489/100000000000000000000)
  directionLo := (14766486643866535731/2500000000000000000)
  directionHi := (590659465754661429241/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree141.table
  base := (126548718582842149930990784821480636811389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-13062857509472427954119143839020640866500000000000)
      constant := (502461696461319282319222799265987655037417522720221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree141.table
  base := (126548718582831295548426402710569969042651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-293486478665697000158749107938824000000000000)
      constant := (11291729238366278890642038163278535043040806659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14766486643866535731/2500000000000000000)
  centralHi := (590659465754661429241/100000000000000000000)
  directionLo := (148191302569858567913/25000000000000000000)
  directionHi := (592765210279434271653/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree142.table
  base := (64632022679229043101625384888357033192013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-6577728618950618679854674976613899379500000000000)
      constant := (254862517395239775866451133810956157974080434661357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree142.table
  base := (129264045358448887254164918226257156146581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-295566940131831986003849155123304000000000000)
      constant := (11454955607565128437937351534170964351615746029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148191302569858567913/25000000000000000000)
  centralHi := (592765210279434271653/100000000000000000000)
  directionLo := (594863500771111188329/100000000000000000000)
  directionHi := (59486350077111118833/10000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree143.table
  base := (3300166501465006333818161484406813079433/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-3312014241582511691324889016858739162875000000000)
      constant := (129260173351663805776300432910186744496890480147370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree143.table
  base := (8250416253662028608878494537325133214533/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-74411850399491742962237300576946000000000000)
      constant := (2904839435065482391340304508887073196798492788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594863500771111188329/100000000000000000000)
  centralHi := (59486350077111118833/10000000000000000000)
  directionLo := (9327412747379937837/1562500000000000000)
  directionHi := (596954415832316021569/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree144.table
  base := (26955312536653439297636806135276672856371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-13340656694758856170889762181642114544000000000000)
      constant := (524408672309846114488166938845626958701189638272095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree144.table
  base := (33694140670815147612119284764475268280953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-74931965766025489423512312373066000000000000)
      constant := (2946233909114169573446605694061555028601196977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9327412747379937837/1562500000000000000)
  centralHi := (596954415832316021569/100000000000000000000)
  directionLo := (29951901634693478383/5000000000000000000)
  directionHi := (599038032693869567661/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree145.table
  base := (68786876616229159296029413547888322226203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-6716628211593832788239984147924636218250000000000)
      constant := (265914485750026075609543164630019075882809102090267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree145.table
  base := (68786876616226360433250808963200599857451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-150904162265118471769574648338372000000000000)
      constant := (5975844648074686518756503935169070484999579859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29951901634693478383/5000000000000000000)
  centralHi := (599038032693869567661/100000000000000000000)
  directionLo := (4808915417984601097/800000000000000000)
  directionHi := (300557213624037568563/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree146.table
  base := (70199115853086864724865755461315228678817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-6762928075808237491035087205028215164500000000000)
      constant := (269650795488636673513831754090110840158022249144513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree146.table
  base := (35099557926542246589084649668312047364227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-75972196499092982346062335965306000000000000)
      constant := (3029904679835003545596450274896704541046113643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4808915417984601097/800000000000000000)
  centralHi := (300557213624037568563/50000000000000000000)
  directionLo := (120636734816194571723/20000000000000000000)
  directionHi := (75397959260121607327/12500000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree147.table
  base := (143249998104414118984604701548606827462633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-13618455880045284387660380524263588221500000000000)
      constant := (546826530741509788195366656328560287992778674574537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree147.table
  base := (71624999052205050114184876927703689861529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-152984623731253457614674695522852000000000000)
      constant := (6144361953014301866046832291102383664821034961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120636734816194571723/20000000000000000000)
  centralHi := (75397959260121607327/12500000000000000000)
  directionLo := (18913932703237547197/3125000000000000000)
  directionHi := (121049169300720302061/20000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree148.table
  base := (18266131553397581389200255971878047126131/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-3427763902118523448312646659617686528500000000000)
      constant := (138600947698190405070262870919040586054886222814118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree148.table
  base := (146129052427177246233493996768436184320999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-308049708928641901074449438230184000000000000)
      constant := (12459004856215145011792873365639209241757686191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18913932703237547197/3125000000000000000)
  centralHi := (121049169300720302061/20000000000000000000)
  directionLo := (607301016582304950447/100000000000000000000)
  directionHi := (37956313536394059403/6250000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree149.table
  base := (149035394674474874854326917850217068242557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-13803655336902903198840792752677904006500000000000)
      constant := (562033371131029037004067919460843319416132931473373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree149.table
  base := (149035394674471990209086545301352957612573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-310130170394776886919549485414664000000000000)
      constant := (12630461569899642419920614436940396457933717557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607301016582304950447/100000000000000000000)
  centralHi := (37956313536394059403/6250000000000000000)
  directionLo := (609349255168118593341/100000000000000000000)
  directionHi := (304674627584059296671/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree150.table
  base := (9498064052893665620871520978686371150899/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-3474063766332928151107749716721265474750000000000)
      constant := (142428817939078067735236225247077181482473708322444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree150.table
  base := (3039380496925924122902698592457898634869/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-156105315930455936382324766299572000000000000)
      constant := (6401547023541050610257381384176155931633675525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609349255168118593341/100000000000000000000)
  centralHi := (304674627584059296671/50000000000000000000)
  directionLo := (611390631925269833109/100000000000000000000)
  directionHi := (61139063192526983311/10000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree151.table
  base := (4841560716957940143324830226624223924157/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-3497213698440130502505301245273054947875000000000)
      constant := (144362373167152896436585422596844418375567099656184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree151.table
  base := (77464971471326007184737904098754946730427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-157145546663523429304874789891812000000000000)
      constant := (6488451143881263684788105766750794645365769443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611390631925269833109/100000000000000000000)
  centralHi := (61139063192526983311/10000000000000000000)
  directionLo := (153356303839706212759/25000000000000000000)
  directionHi := (613425215358824851037/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree152.table
  base := (78959074481771741795928773205760466884299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-7040727261094665707805705547649688842000000000000)
      constant := (292618016933963634827444923752460730911451855063211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree152.table
  base := (157918148963541729916511641750442704047861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-316371554793181844454849626968104000000000000)
      constant := (13151886291940927370036597244565441555670441549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153356303839706212759/25000000000000000000)
  centralHi := (613425215358824851037/100000000000000000000)
  directionLo := (123090614568302569631/20000000000000000000)
  directionHi := (153863268210378212039/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree153.table
  base := (8046682145448465246072126780625840788569/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-3543513562654535205300404302376633894125000000000)
      constant := (148268723838564907514800068367304414167447887156205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree153.table
  base := (160933642908967819451264759978871277435701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-318452016259316830299949674152584000000000000)
      constant := (13328046059617308150757967625663241418316884109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123090614568302569631/20000000000000000000)
  centralHi := (153863268210378212039/25000000000000000000)
  directionLo := (308737135319878709759/50000000000000000000)
  directionHi := (617474270639757419519/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree154.table
  base := (81988212389467061805057224147819117129481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-7133326989523475113395911661856846734500000000000)
      constant := (300483038563804494495914918744043179108925290695209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree154.table
  base := (163976424778932865379323743999105091333437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-320532477725451816145049721337064000000000000)
      constant := (13505381590791676965717621001150702201555624533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308737135319878709759/50000000000000000000)
  centralHi := (617474270639757419519/100000000000000000000)
  directionLo := (309744436969471763037/50000000000000000000)
  directionHi := (24779554957557741043/4000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree155.table
  base := (41761623643360150424914915019229391762421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-3589813426868939908095507359480212840375000000000)
      constant := (152227394796993919841591010085807658961124335912869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree155.table
  base := (167046494573439535990890338148286040776413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-322612939191586801990149768521544000000000000)
      constant := (13683892885464041310142734070870855488540944117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309744436969471763037/50000000000000000000)
  centralHi := (24779554957557741043/4000000000000000000)
  directionLo := (155374236716986830239/25000000000000000000)
  directionHi := (621496946867947320957/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree156.table
  base := (85071926146245731638789973714544193642787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-7225926717952284518986117776064004627000000000000)
      constant := (308452700767680020927896922743461386320008990755843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree156.table
  base := (170143852292490560670254099016005254933253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-324693400657721787835249815706024000000000000)
      constant := (13863579943634408850873776199283862761107507677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155374236716986830239/25000000000000000000)
  centralHi := (621496946867947320957/100000000000000000000)
  directionLo := (9742164883171171027/1562500000000000000)
  directionHi := (623498552522954945729/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree157.table
  base := (173268497936089473792686422519926896379797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-14544453164333378443562441666335167146500000000000)
      constant := (624953544169762422305734426264386542619503987743733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree157.table
  base := (173268497936088709356083984608686577998471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-326773862123856773680349862890504000000000000)
      constant := (14044442765302787368668468489429768597597705039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9742164883171171027/1562500000000000000)
  centralHi := (623498552522954945729/100000000000000000000)
  directionLo := (312746876495297662853/50000000000000000000)
  directionHi := (625493752990595325707/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree158.table
  base := (44105107876059355739619105834084095909261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-3659263223190546962288161945135581259750000000000)
      constant := (158263501772795792399082554041781089958954796027629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree158.table
  base := (88210215752118387783769829537869512948783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-164427161794995879762724955037492000000000000)
      constant := (7113240675234592355261065218952131461873131447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312746876495297662853/50000000000000000000)
  centralHi := (625493752990595325707/100000000000000000000)
  directionLo := (313741304685205479401/50000000000000000000)
  directionHi := (627482609370410958803/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree159.table
  base := (35919930599387622133002304632126625536517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6767192)
      previous := (3383596)
      next := (3383596)
      square := (31207622956130628305154717217060000000000000)
      linear := (-5243735358202562212439606228105903500000000000)
      constant := (228268704271848570267141890967731844368181366785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree159.table
  base := (89799826498468781210124051343506563638959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (76)
      previous := (38)
      next := (38)
      square := (350482052920314327004724930000000000000)
      linear := (-58906156115366099211561046148000000000000)
      constant := (2564915574783483223635912821695506563638959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313741304685205479401/50000000000000000000)
  centralHi := (627482609370410958803/100000000000000000000)
  directionLo := (314732590898344853409/50000000000000000000)
  directionHi := (629465181796689706819/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree160.table
  base := (11425385150887145963265789491898968442809/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-3705563087404951665083265002239160206000000000000)
      constant := (162352973448770291284230892714338304492339277058404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree160.table
  base := (22850770301774233893490732160640705831691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-83253811630565432803912501110986000000000000)
      constant := (3648521452824016839231815409652239485362440038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314732590898344853409/50000000000000000000)
  centralHi := (629465181796689706819/100000000000000000000)
  directionLo := (631441529459679658851/100000000000000000000)
  directionHi := (157860382364919914713/25000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree161.table
  base := (93019979878004442427703630104471203188681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-7457426039024308032961633061581899358250000000000)
      constant := (328834658788779555994315986518316868880374428944009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree161.table
  base := (46509989939002122930649789010310852906969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-83773926997099179265187512907106000000000000)
      constant := (3694912921739142091793915586463219185815675921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631441529459679658851/100000000000000000000)
  centralHi := (157860382364919914713/25000000000000000000)
  directionLo := (633411710626208241343/100000000000000000000)
  directionHi := (9897057978534503771/1562500000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree162.table
  base := (23662630627798066014765713491228449457513/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-3751862951619356367878368059342739152250000000000)
      constant := (166494765411764205185178865642018015995853430981714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree162.table
  base := (94650522511192097615646582047163359282691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-168588084727265851452925049406452000000000000)
      constant := (7483196663057559782557607021446225876225079019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633411710626208241343/100000000000000000000)
  centralHi := (9897057978534503771/1562500000000000000)
  directionLo := (127075156531945179133/20000000000000000000)
  directionHi := (317687891329862947833/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree163.table
  base := (96294709106662004792150246358985521037329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-7550025767453117438551839175789057250750000000000)
      constant := (337170563001787317302210628772134626474272427164881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree163.table
  base := (38517883642664745544334232571626786612361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-339256630920666688750950145997384000000000000)
      constant := (15154310728771728664393802887218930217970610245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127075156531945179133/20000000000000000000)
  centralHi := (317687891329862947833/50000000000000000000)
  directionLo := (19916681313743557189/3125000000000000000)
  directionHi := (637333802039793830049/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree164.table
  base := (195905079328830043925420348885054976362761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-15192651263335044282693884465785272394000000000000)
      constant := (682755510647112893075178541947501051163083969289129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree164.table
  base := (48976269832207451318760021710008147442507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (492252043326581472278136164185000000000000)
      linear := (-85334273096700418649012548295466000000000000)
      constant := (3835850973731600823620955014465876886166002163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19916681313743557189/3125000000000000000)
  centralHi := (637333802039793830049/100000000000000000000)
  directionLo := (127857164876206915187/20000000000000000000)
  directionHi := (9988841005953665249/1562500000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree165.table
  base := (199248028368905312159289608726189721653027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-15285250991763853688284090579992430286500000000000)
      constant := (691222215577671931439703925476580152836120416923203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree165.table
  base := (199248028368905110103776374181992549734517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-343417553852936660441150240366344000000000000)
      constant := (15533672824579150989719830969566977072204258253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127857164876206915187/20000000000000000000)
  centralHi := (9988841005953665249/1562500000000000000)
  directionLo := (641231904451563337591/100000000000000000000)
  directionHi := (80153988056445417199/12500000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree166.table
  base := (202618265333552458568609480191995511413361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-15377850720192663093874296694199588179000000000000)
      constant := (699741240795252080390640792737493861598211094432529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree166.table
  base := (202618265333552287502723410191595516071977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-345498015319071646286250287550824000000000000)
      constant := (15725117517729979180735050691658335804646183393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641231904451563337591/100000000000000000000)
  centralHi := (80153988056445417199/12500000000000000000)
  directionLo := (321586048095458708103/50000000000000000000)
  directionHi := (643172096190917416207/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree167.table
  base := (206015790222774088335408895909182762738943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87662212883770934909179600662721540000000000000)
      linear := (-15470450448621472499464502808406746071500000000000)
      constant := (708312586299853665730722434027754009962256076980127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree167.table
  base := (206015790222773943511443110554412905216571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-347578476785206632131350334735304000000000000)
      constant := (15917737974378895187894608645298353850753347939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321586048095458708103/50000000000000000000)
  centralHi := (643172096190917416207/100000000000000000000)
  directionLo := (322553226363750157019/50000000000000000000)
  directionHi := (645106452727500314039/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree168.table
  base := (10472030151828638288521660986078867338123/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21915553220942733727294900165680385000000000000)
      linear := (-3890762544262570476263677230653475991000000000000)
      constant := (179234063022869252037835075439697134294272262995735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree168.table
  base := (104720301518286321583594549055753746327563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (213484)
      previous := (106742)
      next := (106742)
      square := (984504086653162944556272328370000000000000)
      linear := (-174829469125670808988225190959892000000000000)
      constant := (8055767097262953108194075128523788273434124467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell146.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322553226363750157019/50000000000000000000)
  centralHi := (645106452727500314039/100000000000000000000)
  directionLo := (647035026395556478769/100000000000000000000)
  directionHi := (64703502639555647877/10000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree169.table
  base := (21289270377495101303604250701263312998899/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43831106441885467454589800331360770000000000000)
      linear := (-7827824952739545655322457518410530928250000000000)
      constant := (362806119085061211536415159745431941421454645013055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree169.table
  base := (212892703774950909247797171572303837837539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1969008173306325889112544656740000000000000)
      linear := (-351739399717476603821550429104264000000000000)
      constant := (16306506178171019352698616285480777480485647051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell146.Kernel169
