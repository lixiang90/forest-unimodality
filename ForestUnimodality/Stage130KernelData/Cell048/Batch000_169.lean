import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell048.Parameters
import ForestUnimodality.BinomialMassData.Q47_97.Batch000_049
import ForestUnimodality.BinomialMassData.Q47_97.Batch050_099
import ForestUnimodality.BinomialMassData.Q47_97.Batch100_149
import ForestUnimodality.BinomialMassData.Q47_97.Batch150_199
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch000_049
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch050_099
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch100_149
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree000.table
  base := (103670722252276035409135347/1250000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (166)
      previous := (83)
      next := (83)
      square := (661073643689564366399125110000000000000)
      linear := (26751661897419843662293548000000000000)
      constant := (829365778018208283273082776000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree000.table
  base := (103670722252276035409135347/1250000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (166)
      previous := (83)
      next := (83)
      square := (661073643689564366399125110000000000000)
      linear := (26751661897419843662293548000000000000)
      constant := (829365778018208283273082776000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree001.table
  base := (475934010341116610981717959304545050672869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-5775963096368624583808702759848000000000000)
      constant := (4479401454151886103345103550179122381781024421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree001.table
  base := (474977522258730023709380729599161608636261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-13907363432236773868643383346992923000000000000)
      constant := (10733453122330241079312512800942906610531249977349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49976081004292051691/100000000000000000000)
  directionHi := (12494020251073012923/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree002.table
  base := (28597650539436161198394743444624149073971/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-11803632579530072476635925512828000000000000)
      constant := (2696350264318008723763951287605982186369931390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree002.table
  base := (284951914966691733613648324610608782947779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-28419073899163116502240233197495778000000000000)
      constant := (6450865089594450073839676041657490594552321919011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49976081004292051691/100000000000000000000)
  centralHi := (12494020251073012923/25000000000000000000)
  directionLo := (17669212887631557023/25000000000000000000)
  directionHi := (70676851550526228093/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree003.table
  base := (45405486168423196371566020705468106722111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-17831302062691520369463148265808000000000000)
      constant := (1721657800065196636606870572726911664593369596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree003.table
  base := (45195479605568371733856255439127087696451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-42930784366089459135837083047998633000000000000)
      constant := (4114892461602181047092963675534353259552255236236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669212887631557023/25000000000000000000)
  centralHi := (70676851550526228093/100000000000000000000)
  directionLo := (43280555731305838149/50000000000000000000)
  directionHi := (86561111462611676299/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree004.table
  base := (122470421384850370775312517034516537947123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-23858971545852968262290371018788000000000000)
      constant := (1175201338366259753321900565524278105544480307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree004.table
  base := (15230042171535744509278651356229717993669/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-57442494833015801769433932898501488000000000000)
      constant := (2807725904743876620545947242503976084099506576168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43280555731305838149/50000000000000000000)
  centralHi := (86561111462611676299/100000000000000000000)
  directionLo := (49976081004292051691/50000000000000000000)
  directionHi := (99952162008584103383/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree005.table
  base := (43754152693811739081836589721112690119233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-29886641029014416155117593771768000000000000)
      constant := (859263633231953812840110648144988602663726594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree005.table
  base := (43523884577333285819059024307343519515421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-71954205299942144403030782749004343000000000000)
      constant := (2053160443766257330502121442634688505304102899578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49976081004292051691/50000000000000000000)
  centralHi := (99952162008584103383/100000000000000000000)
  directionLo := (22349982874926597339/20000000000000000000)
  directionHi := (13968739296829123337/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree006.table
  base := (13145148707141788148289942388018567090343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-35914310512175864047944816524748000000000000)
      constant := (670252976408712317706285987179981488765186435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree006.table
  base := (510833491191318569654167019097453728203/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-86465915766868487036627632599507198000000000000)
      constant := (1602299029383113261956183757803783514017443433856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22349982874926597339/20000000000000000000)
  centralHi := (13968739296829123337/12500000000000000000)
  directionLo := (61207948902257305333/50000000000000000000)
  directionHi := (122415897804514610667/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree007.table
  base := (25663357102403500602774365894309938734929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-41941979995337311940772039277728000000000000)
      constant := (553634600433498851455620944433310427113893922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree007.table
  base := (1276761334795781164875915769106416262439/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-2060767882322343462657642498979797000000000000)
      constant := (27028891633108031622284552130543173777045559960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61207948902257305333/50000000000000000000)
  centralHi := (122415897804514610667/100000000000000000000)
  directionLo := (33056070459743969243/25000000000000000000)
  directionHi := (132224281838975876973/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree008.table
  base := (10305161216027577259714404293529487878791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-47969649478498759833599262030708000000000000)
      constant := (480329308363947053072602861259979805806178076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree008.table
  base := (41020085741538524219997147898136935622297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-115489336700721172303821332300512908000000000000)
      constant := (1149953093671578535912102640581057699875732127673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33056070459743969243/25000000000000000000)
  centralHi := (132224281838975876973/100000000000000000000)
  directionLo := (17669212887631557023/12500000000000000000)
  directionHi := (28270740620210491237/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree009.table
  base := (33730351543224621606619425801500389613611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-53997318961660207726426484783688000000000000)
      constant := (434556476222617493606803667605519165874465899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree009.table
  base := (16783885589369388435511782727661732591691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-130001047167647514937418182151015763000000000000)
      constant := (1041233667646435957883677727082460511243969412438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669212887631557023/12500000000000000000)
  centralHi := (28270740620210491237/20000000000000000000)
  directionLo := (74964121506438077537/50000000000000000000)
  directionHi := (5997129720515046203/4000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree010.table
  base := (5584527108304215101200205128304410090451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-60024988444821655619253707536668000000000000)
      constant := (407535637435293197300966424206760972705267295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree010.table
  base := (6946709748846953469631734224455203839443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-144512757634573857571015032001518618000000000000)
      constant := (977322985641403131592268396360450487634765471948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74964121506438077537/50000000000000000000)
  centralHi := (5997129720515046203/4000000000000000000)
  directionLo := (79019122251319029157/50000000000000000000)
  directionHi := (31607648900527611663/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree011.table
  base := (23260193214800397917957349061702232502353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-66052657927983103512080930289648000000000000)
      constant := (394211302013703206200696089709694305614639377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree011.table
  base := (23144193137919336974609027608226552362627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-159024468101500200204611881852021473000000000000)
      constant := (946177869912499330771101219089177690838077820643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79019122251319029157/50000000000000000000)
  centralHi := (31607648900527611663/20000000000000000000)
  directionLo := (5179747161988893959/3125000000000000000)
  directionHi := (165751909183644606689/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree012.table
  base := (19419841156954577727851243981530750655657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-72080327411144551404908153042628000000000000)
      constant := (391542637289777243728371700188798832919076713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree012.table
  base := (3863847267087056553377190320043180490459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-173536178568426542838208731702524328000000000000)
      constant := (940555704627490967240261295496605280242918415655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5179747161988893959/3125000000000000000)
  centralHi := (165751909183644606689/100000000000000000000)
  directionLo := (173122222925223352597/100000000000000000000)
  directionHi := (86561111462611676299/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree013.table
  base := (3239391375108068258360657429133684501941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-78107996894305999297735375795608000000000000)
      constant := (397604350232116548168731762234588187393814345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree013.table
  base := (2013610988445488837461572664803061266341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-188047889035352885471805581553027183000000000000)
      constant := (955868692308373926761052727993348650738687424552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173122222925223352597/100000000000000000000)
  centralHi := (86561111462611676299/50000000000000000000)
  directionLo := (90095661303858426973/50000000000000000000)
  directionHi := (180191322607716853947/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree014.table
  base := (13454727079103026860615257952049248433959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-84135666377467447190562598548588000000000000)
      constant := (411109164581424207123570218202223378515120231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree014.table
  base := (6688618992017228861403693974276310983929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-4133869377597535267457192477623062000000000000)
      constant := (20184622282707603445490887900853144884683220178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90095661303858426973/50000000000000000000)
  centralHi := (180191322607716853947/100000000000000000000)
  directionLo := (186993372651722210291/100000000000000000000)
  directionHi := (46748343162930552573/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree015.table
  base := (554838901790239919487082874602862274989/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-90163335860628895083389821301568000000000000)
      constant := (431150299894838021249758468860536622907430020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree015.table
  base := (11028440546295425870272930540303818958697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-217071309969205570738999281254032893000000000000)
      constant := (1037923844992675835931837390816855316205294555273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186993372651722210291/100000000000000000000)
  centralHi := (46748343162930552573/25000000000000000000)
  directionLo := (12097283089895997111/6250000000000000000)
  directionHi := (193556529438335953777/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree016.table
  base := (1810416930845865772796037763534344394089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-96191005343790342976217044054548000000000000)
      constant := (457059481087221769661258102225601232019917005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree016.table
  base := (8991783659710886490005697933990528632943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-231583020436131913372596131104535748000000000000)
      constant := (1100903297776616052166827909658400366261573009487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12097283089895997111/6250000000000000000)
  centralHi := (193556529438335953777/100000000000000000000)
  directionLo := (39980864803433641353/20000000000000000000)
  directionHi := (99952162008584103383/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree017.table
  base := (1816597496367641554916075691530143865613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-102218674826951790869044266807528000000000000)
      constant := (488326204526318408491030557224894494526210868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree017.table
  base := (7213204012310919068340741230988309027843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-246094730903058256006192980955038603000000000000)
      constant := (1176763505437210935480535580113074393517782463587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39980864803433641353/20000000000000000000)
  centralHi := (99952162008584103383/50000000000000000000)
  directionLo := (103028330367560230571/50000000000000000000)
  directionHi := (206056660735120461143/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree018.table
  base := (5697126866119741417634905628680240490371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-108246344310113238761871489560508000000000000)
      constant := (524549955771614829849627921153036382773900739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree018.table
  base := (5650262783417851880132274165119324026669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-260606441369984598639789830805541458000000000000)
      constant := (1264545732194581817831146418329577506660395619021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103028330367560230571/50000000000000000000)
  centralHi := (206056660735120461143/100000000000000000000)
  directionLo := (53007638662894671069/25000000000000000000)
  directionHi := (212030554651578684277/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree019.table
  base := (1077565856476067929140108516265996135137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-114274013793274686654698712313488000000000000)
      constant := (565410528955716302723861514541269030542016132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree019.table
  base := (2134510573963977099962517749250658384743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-275118151836910941273386680656044313000000000000)
      constant := (1363483265745360892466324088585560500026309151374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53007638662894671069/25000000000000000000)
  centralHi := (212030554651578684277/100000000000000000000)
  directionLo := (13615042918244484239/6250000000000000000)
  directionHi := (8713627467676469913/4000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree020.table
  base := (19238980227263096462031415271885940673/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-120301683276436134547525935066468000000000000)
      constant := (610648585425623288742939595296267970526761120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree020.table
  base := (608398018605795656851883331482971210179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-289629862303837283906983530506547168000000000000)
      constant := (1472955101553705555303342882455650539779473403055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13615042918244484239/6250000000000000000)
  centralHi := (8713627467676469913/4000000000000000000)
  directionLo := (223499828749265973391/100000000000000000000)
  directionHi := (13968739296829123337/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree021.table
  base := (395705356535714991724489286872882010691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-126329352759597582440353157819448000000000000)
      constant := (660052231539244862623963585792552734192958095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree021.table
  base := (1946712188575314296321266575187275702911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-6206970872872727072256742456266327000000000000)
      constant := (32499059257409784963433587385005833152345790351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223499828749265973391/100000000000000000000)
  centralHi := (13968739296829123337/6250000000000000000)
  directionLo := (45803834827882600671/20000000000000000000)
  directionHi := (57254793534853250839/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree022.table
  base := (31019470865906840906040412399677175303/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-132357022242759030333180380572428000000000000)
      constant := (713447304851646623156900183518450001357629664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree022.table
  base := (120591661503928702711727020106150528553/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-318653283237689969174177230207552878000000000000)
      constant := (1721562774223375116068950026529455463867164639816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45803834827882600671/20000000000000000000)
  centralHi := (57254793534853250839/25000000000000000000)
  directionLo := (58602149489185942003/25000000000000000000)
  directionHi := (234408597956743768013/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree023.table
  base := (105249061376237818279969300058514184689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-138384691725920478226007603325408000000000000)
      constant := (770690067550432294649027154248324559963738801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree023.table
  base := (80827916219000472960878731726416667821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-333164993704616311807774080058055733000000000000)
      constant := (1859937754266717616599022456354185897855494221389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58602149489185942003/25000000000000000000)
  centralHi := (234408597956743768013/100000000000000000000)
  directionLo := (119838432346006908471/50000000000000000000)
  directionHi := (239676864692013816943/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree024.table
  base := (-87029975926660160506877368933782661677/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-144412361209081926118834826078388000000000000)
      constant := (831661546866183013560557219799888311490248856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree024.table
  base := (-717601437846420454786911120744536356853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-347676704171542654441370929908558588000000000000)
      constant := (2007294253530171824873229853210331564461506665323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119838432346006908471/50000000000000000000)
  centralHi := (239676864692013816943/100000000000000000000)
  directionLo := (244831795609029221333/100000000000000000000)
  directionHi := (122415897804514610667/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree025.table
  base := (-711165966482352091283946011836784622893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-150440030692243374011662048831368000000000000)
      constant := (896263057496881475024600901809705386966399526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree025.table
  base := (-288199962611653696780749952197241946039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-362188414638468997074967779759061443000000000000)
      constant := (2163396307955726757483350665841455246484277183245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244831795609029221333/100000000000000000000)
  centralHi := (122415897804514610667/50000000000000000000)
  directionLo := (249880405021460258457/100000000000000000000)
  directionHi := (124940202510730129229/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree026.table
  base := (-2081741604091869692506106224753246928919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-156467700175404821904489271584348000000000000)
      constant := (964412606699078269628494883873904699645801129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree026.table
  base := (-5245104275024590290343869056814922051/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-376700125105395339708564629609564298000000000000)
      constant := (2328047951822408838182765333908028129344624216400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249880405021460258457/100000000000000000000)
  centralHi := (124940202510730129229/50000000000000000000)
  directionLo := (254829012253778871009/100000000000000000000)
  directionHi := (25482901225377887101/10000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree027.table
  base := (-2681718849824998135297022142857906466331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-162495369658566269797316494337328000000000000)
      constant := (1036041978949628054367929130218595958058291621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree027.table
  base := (-21567526605231375600368983273053103171/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-391211835572321682342161479460067153000000000000)
      constant := (2501086220437434121256266799361922066473251307625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254829012253778871009/100000000000000000000)
  centralHi := (25482901225377887101/10000000000000000000)
  directionLo := (8115104199619844653/3125000000000000000)
  directionHi := (259683334387835028897/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree028.table
  base := (-3228302430086560905679471029795828539637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-168523039141727717690143717090308000000000000)
      constant := (1111094355556420295889805977595515049270555467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree028.table
  base := (-3240702927019003486979136310537548545203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-8280072368147918877056292434909592000000000000)
      constant := (54742355866608374861521782967364244081171063677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8115104199619844653/3125000000000000000)
  centralHi := (259683334387835028897/100000000000000000000)
  directionLo := (52889712735590350789/20000000000000000000)
  directionHi := (132224281838975876973/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree029.table
  base := (-186326368533982894658824029391679068741/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-174550708624889165582970939843288000000000000)
      constant := (1189522361961673627333603258354035832844318620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree029.table
  base := (-3737333239828372505056272050794131236969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-420235256506174367609355179161072863000000000000)
      constant := (2871802529802175662988539242646642720453452188279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52889712735590350789/20000000000000000000)
  centralHi := (132224281838975876973/50000000000000000000)
  directionLo := (6728235815570418927/2500000000000000000)
  directionHi := (269129432622816757081/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree030.table
  base := (-2090297884179050961677844595304613105403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-180578378108050613475798162596268000000000000)
      constant := (1271286460637031423823555063036597790582526346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree030.table
  base := (-4190007077252923332001044328203066409229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-434746966973100710242952029011575718000000000000)
      constant := (3069273172915108513282531572333845300421509977939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6728235815570418927/2500000000000000000)
  centralHi := (269129432622816757081/100000000000000000000)
  directionLo := (273730269017561931339/100000000000000000000)
  directionHi := (13686513450878096567/5000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree031.table
  base := (-2297008850904525673053868672590814782979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-186606047591212061368625385349248000000000000)
      constant := (1356353625252126212445540355112284047413901178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree031.table
  base := (-4602210551691622942442395843673337682651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-449258677440027052876548878862078573000000000000)
      constant := (3274708612006028844581999138245736542726192115141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273730269017561931339/100000000000000000000)
  centralHi := (13686513450878096567/5000000000000000000)
  directionLo := (139127521404801848631/50000000000000000000)
  directionHi := (278255042809603697263/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree032.table
  base := (-248486384588623152422026705772676321693/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-192633717074373509261452608102228000000000000)
      constant := (1444696244901315738849701718198833769783811260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree032.table
  base := (-2488428410931528766519132132925274933379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-463770387906953395510145728712581428000000000000)
      constant := (3488043035880106647650966700588504571305121221178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139127521404801848631/50000000000000000000)
  centralHi := (278255042809603697263/100000000000000000000)
  directionLo := (17669212887631557023/6250000000000000000)
  directionHi := (282707406202104912369/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree033.table
  base := (-5310181093364058834531319908578401858433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-198661386557534957154279830855208000000000000)
      constant := (1536291217148316176580535497305339816914003903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree033.table
  base := (-2658191133390956157163379968381645142107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-478282098373879738143742578563084283000000000000)
      constant := (3709221404277093757766000913782388491694708968074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669212887631557023/6250000000000000000)
  centralHi := (282707406202104912369/100000000000000000000)
  directionLo := (71772682039403712427/25000000000000000000)
  directionHi := (287090728157614849709/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree034.table
  base := (-5617433976925179674430021578975762386081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-204689056040696405047107053608188000000000000)
      constant := (1631119196427285848450841930658569051709363871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree034.table
  base := (-1405706537480815400925198814495934874087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-492793808840806080777339428413587138000000000000)
      constant := (3938197648177471399747209637227259558684346864868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71772682039403712427/25000000000000000000)
  centralHi := (287090728157614849709/100000000000000000000)
  directionLo := (58281624845783793149/20000000000000000000)
  directionHi := (145704062114459482873/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree035.table
  base := (-736651174741511924886426277031114960483/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-210716725523857852939934276361168000000000000)
      constant := (1729163970509248531621167577076443914694523624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree035.table
  base := (-2948948339675919372681536838412394550153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-10353173863423110681855842413552857000000000000)
      constant := (85202717906887251225165499990215126783405821454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58281624845783793149/20000000000000000000)
  centralHi := (145704062114459482873/50000000000000000000)
  directionLo := (73915620617010240663/25000000000000000000)
  directionHi := (295662482468040962653/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree036.table
  base := (-6138952430177950628927555310477390369443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-216744395007019300832761499114148000000000000)
      constant := (1830411942694884528358055274726806234013910813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree036.table
  base := (-6143025841675896797248149752552836585167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-521817229774658766044533128114592848000000000000)
      constant := (4419395642034750564317623457202855233728963036497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73915620617010240663/25000000000000000000)
  centralHi := (295662482468040962653/100000000000000000000)
  directionLo := (74964121506438077537/25000000000000000000)
  directionHi := (299856486025752310149/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree037.table
  base := (-6355875910651613969746577908121068927631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-222772064490180748725588721867128000000000000)
      constant := (1934851701400965573949456412683514862459919921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree037.table
  base := (-6359414960562027658873044408380512453497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-536328940241585108678129977965095703000000000000)
      constant := (4671557902855533271999435394944716778113437191527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74964121506438077537/25000000000000000000)
  centralHi := (299856486025752310149/100000000000000000000)
  directionLo := (15199631647202815627/5000000000000000000)
  directionHi := (303992632944056312541/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree038.table
  base := (-6544998498202602186808749012082971457793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-228799733973342196618415944620108000000000000)
      constant := (2042473662066376565151037101080255321553625663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree038.table
  base := (-3274036291581816352536978089182422710089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-550840650708511451311726827815598558000000000000)
      constant := (4931397175802004018239008378137456703329150020398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15199631647202815627/5000000000000000000)
  centralHi := (303992632944056312541/100000000000000000000)
  directionLo := (308073253556369791113/100000000000000000000)
  directionHi := (154036626778184895557/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree039.table
  base := (-6707176365314655634240854904809485864489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-234827403456503644511243167373088000000000000)
      constant := (2153269768964217988970818407785489547501022999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree039.table
  base := (-1677461503565416951586257117704736985357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-565352361175437793945323677666101413000000000000)
      constant := (5198894319404230485937406378596582811059668579148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308073253556369791113/100000000000000000000)
  centralHi := (154036626778184895557/50000000000000000000)
  directionLo := (78025131459900018307/25000000000000000000)
  directionHi := (312100525839600073229/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree040.table
  base := (-3421564805413972520806047705915885454079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-240855072939665092404070390126068000000000000)
      constant := (2267233246684502679014283731640794867525141378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree040.table
  base := (-6845447585865927890707533928600238156809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-579864071642364136578920527516604268000000000000)
      constant := (5474033241363368409787546473855849382397384469719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78025131459900018307/25000000000000000000)
  centralHi := (312100525839600073229/100000000000000000000)
  directionLo := (316076489005276116629/100000000000000000000)
  directionHi := (31607648900527611663/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree041.table
  base := (-6953464291575329367120350734871432867519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-246882742422826540296897612879048000000000000)
      constant := (2384358392838490265343749217828172688149513729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree041.table
  base := (-3477738279879383984615782351023962767733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-594375782109290479212517377367107123000000000000)
      constant := (5756800403751099251693149112516113983171957774806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316076489005276116629/100000000000000000000)
  centralHi := (31607648900527611663/10000000000000000000)
  directionLo := (32000305557048981823/10000000000000000000)
  directionHi := (320003055570489818231/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree042.table
  base := (-7038690814912742877545870538231938319453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-252910411905987988189724835632028000000000000)
      constant := (2504640405003368762443079497256191692352266723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree042.table
  base := (-7040437404222142032079259637960130330127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-12426275358698302486655392392196122000000000000)
      constant := (123411926737141330092344398049594095052467917793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32000305557048981823/10000000000000000000)
  centralHi := (320003055570489818231/100000000000000000000)
  directionLo := (20242626381965216751/6250000000000000000)
  directionHi := (323882022111443468017/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree043.table
  base := (-1419847861163324869862234346413223663963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-258938081389149436082552058385008000000000000)
      constant := (2628075236133234857864915108317223892728860665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree043.table
  base := (-1420151011545695914677126799210446847971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-623399203043143164479711077068112833000000000000)
      constant := (6345175660680991077328856072650471880192327536305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20242626381965216751/6250000000000000000)
  centralHi := (323882022111443468017/100000000000000000000)
  directionLo := (327715078871182118173/100000000000000000000)
  directionHi := (163857539435591059087/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree044.table
  base := (-1427094491313020823953710562731516220379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-264965750872310883975379281137988000000000000)
      constant := (2754659473656443623265108274450327819412269945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree044.table
  base := (-3568393843320886881360244094569691538867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-637910913510069507113307926918615688000000000000)
      constant := (6650766064094744493135400929923086976636463506394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327715078871182118173/100000000000000000000)
  centralHi := (163857539435591059087/50000000000000000000)
  directionLo := (5179747161988893959/1562500000000000000)
  directionHi := (331503818367289213377/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree045.table
  base := (-446731017495565059522327328415191420089/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-270993420355472331868206503890968000000000000)
      constant := (2884390238298834048538459342010873422854121584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree045.table
  base := (-7148837356860535610630438351825229571493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-652422623976995849746904776769118543000000000000)
      constant := (6963948796387753566618652376231579616698335493563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5179747161988893959/1562500000000000000)
  centralHi := (331503818367289213377/100000000000000000000)
  directionLo := (335249743123898960087/100000000000000000000)
  directionHi := (41906217890487370011/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree046.table
  base := (-892021139368072120713405304416916451961/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-277021089838633779761033726643948000000000000)
      constant := (3017265099348415072490778477467497864827991608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree046.table
  base := (-1427431793498630426323542783466654961991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-666934334443922192380501626619621398000000000000)
      constant := (7284718099131966634758507415929932788268833305405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335249743123898960087/100000000000000000000)
  centralHi := (41906217890487370011/12500000000000000000)
  directionLo := (16947713631725357227/5000000000000000000)
  directionHi := (338954272634507144541/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree047.table
  base := (-7101109175001859164655195518254056561477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-283048759321795227653860949396928000000000000)
      constant := (3153282003635398801953557855848053581813062907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree047.table
  base := (-7101967735357454753617675868409294945261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-681446044910848535014098476470124253000000000000)
      constant := (7613069110362315116405995457638687817582954241651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16947713631725357227/5000000000000000000)
  centralHi := (338954272634507144541/100000000000000000000)
  directionLo := (85654687411772509399/25000000000000000000)
  directionHi := (342618749647090037597/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree048.table
  base := (-1760675219735330843616557915241181242533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-289076428804956675546688172149908000000000000)
      constant := (3292439215962915576246877820455006902756028012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree048.table
  base := (-3521722735053545350322001954291576168817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-695957755377774877647695326320627108000000000000)
      constant := (7948997722815277180240598447052284252292139267294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85654687411772509399/25000000000000000000)
  centralHi := (342618749647090037597/100000000000000000000)
  directionLo := (69248889170089341039/20000000000000000000)
  directionHi := (86561111462611676299/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree049.table
  base := (-6961100165278528216471319397314991726331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-295104098288118123439515394902888000000000000)
      constant := (3434735269105472504302635288353385242846951621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree049.table
  base := (-348087291963996427309789352009497664757/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-295905650081091720233774334098763000000000000)
      constant := (3453769456470687975625814786766834104446027740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69248889170089341039/20000000000000000000)
  centralHi := (86561111462611676299/25000000000000000000)
  directionLo := (4372907087875554523/1250000000000000000)
  directionHi := (349832567030044361841/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree050.table
  base := (-1714109739022061576153740779731090063569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-301131767771279571332342617655868000000000000)
      constant := (3580168921808268050596226417722440694367517116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree050.table
  base := (-1371399757808133120512395521810152736007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-724981176311627562914889026021632818000000000000)
      constant := (8643574401259872871652748492518326303747456194685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4372907087875554523/1250000000000000000)
  centralHi := (349832567030044361841/100000000000000000000)
  directionLo := (17669212887631557023/5000000000000000000)
  directionHi := (353384257752631140461/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree051.table
  base := (-841103613655443282679509313651537903503/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-307159437254441019225169840408848000000000000)
      constant := (3728739123482374512458182588532879438927522184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree051.table
  base := (-3364657129311413108059488372189796059393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-739492886778553905548485875872135673000000000000)
      constant := (9002217047998316305155391620228073277403176404926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669212887631557023/5000000000000000000)
  centralHi := (353384257752631140461/100000000000000000000)
  directionLo := (356900605631211563437/100000000000000000000)
  directionHi := (178450302815605781719/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree052.table
  base := (-822295571827506029704408750499772881913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-313187106737602467117997063161828000000000000)
      constant := (3880444984508012179890561700740077095632644664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree052.table
  base := (-6578785303456252534852244219472289164509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-754004597245480248182082725722638528000000000000)
      constant := (9368426302985399067151791832548745086233974700419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356900605631211563437/100000000000000000000)
  centralHi := (178450302815605781719/50000000000000000000)
  directionLo := (360382645215433707893/100000000000000000000)
  directionHi := (180191322607716853947/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree053.table
  base := (-6405126050712631494418755115793859599129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-319214776220763915010824285914808000000000000)
      constant := (4035285751238442733924674566676809575031795239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree053.table
  base := (-1281098144573341862330060905948839933711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-768516307712406590815679575573141383000000000000)
      constant := (9742200386064843612177561696607693215964876978005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360382645215433707893/100000000000000000000)
  centralHi := (180191322607716853947/50000000000000000000)
  directionLo := (181915680773415410401/50000000000000000000)
  directionHi := (363831361546830820803/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree054.table
  base := (-1552295305547874403817637056299182925183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-325242445703925362903651508667788000000000000)
      constant := (4193260784946804247861520057400035951427812612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree054.table
  base := (-6209497272373313090547511913668635107453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-783028018179332933449276425423644238000000000000)
      constant := (10123537789162116778714372219494378940769813309923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181915680773415410401/50000000000000000000)
  centralHi := (363831361546830820803/100000000000000000000)
  directionLo := (45905961676692979/12500000000000000)
  directionHi := (367247693413543832001/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree055.table
  base := (-5990587645686717082935166487203024215379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-331270115187086810796478731420768000000000000)
      constant := (4354369544082764388528955010998396745157498989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree055.table
  base := (-2995430763713362823022563144868462986849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-797539728646259276082873275274147093000000000000)
      constant := (10512437234180703487558509467878825347070854718718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45905961676692979/12500000000000000)
  centralHi := (367247693413543832001/100000000000000000000)
  directionLo := (185316268167500506767/50000000000000000000)
  directionHi := (74126507267000202707/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree056.table
  base := (-574939414007385376919548750378259522297/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-337297784670248258689305954173748000000000000)
      constant := (4518611569309522975457374332114957561547075270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree056.table
  base := (-718703931808108344837152416217791199821/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-16572478349248686096254492349482652000000000000)
      constant := (222630564030823938673595885380345018619546610712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185316268167500506767/50000000000000000000)
  centralHi := (74126507267000202707/20000000000000000000)
  directionLo := (186993372651722210291/50000000000000000000)
  directionHi := (373986745303444420583/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree057.table
  base := (-5485642128357524124790690779575410265257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-343325454153409706582133176926728000000000000)
      constant := (4685986470878029572461773080790560964814196887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree057.table
  base := (-109716954720657275729887534919301432647/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-826563149580111961350066974975152803000000000000)
      constant := (11312918080091382186006927423027226648442936458850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186993372651722210291/50000000000000000000)
  centralHi := (373986745303444420583/100000000000000000000)
  directionLo := (188655568653042261729/50000000000000000000)
  directionHi := (377311137306084523459/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree058.table
  base := (-5199366770600820231131589987889217231609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-349353123636571154474960399679708000000000000)
      constant := (4856493917967250546148156911173054355067790919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree058.table
  base := (-10155361111535599986757875684633168811/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-841074860047038303983663824825655658000000000000)
      constant := (11724497782150426650893770858749121503406396006912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188655568653042261729/50000000000000000000)
  centralHi := (377311137306084523459/100000000000000000000)
  directionLo := (380606493648963547301/100000000000000000000)
  directionHi := (190303246824481773651/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree059.table
  base := (-122264948024176492937259716891667312061/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-355380793119732602367787622432688000000000000)
      constant := (5030133629679363240942703660089254090432722040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree059.table
  base := (-4890752209411709538566230873477101187631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-855586570513964646617260674676158513000000000000)
      constant := (12143636081867479661049952671078002482151317390321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380606493648963547301/100000000000000000000)
  centralHi := (190303246824481773651/50000000000000000000)
  directionLo := (383873562101255014149/100000000000000000000)
  directionHi := (7677471242025100283/2000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree060.table
  base := (-1139840234152980657414973595999368708643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-361408462602894050260614845185668000000000000)
      constant := (5206905367428889863294548801385047759281512052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree060.table
  base := (-4559494569244860271215667632019124761809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-870098280980890989250857524526661368000000000000)
      constant := (12570332417352288608220337051958310594333850024719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383873562101255014149/100000000000000000000)
  centralHi := (7677471242025100283/2000000000000000000)
  directionLo := (387113058876671907553/100000000000000000000)
  directionHi := (193556529438335953777/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree061.table
  base := (-4205677361711308074065580593535117102747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-367436132086055498153442067938648000000000000)
      constant := (5386808928506679378511335055080966083180253477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree061.table
  base := (-2102896545929928276375496399096824227583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-884609991447817331884454374377164223000000000000)
      constant := (13004586311409228266860015897109742676381508797506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387113058876671907553/100000000000000000000)
  centralHi := (193556529438335953777/50000000000000000000)
  directionLo := (97581417616714175943/25000000000000000000)
  directionHi := (390325670466856703773/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree062.table
  base := (-1914782753093150944809417813249624369967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-373463801569216946046269290691628000000000000)
      constant := (5569844140634684289934745168453244568605960994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree062.table
  base := (-3829665721809203273374921722945383564409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-899121701914743674518051224227667078000000000000)
      constant := (13446397358652751498021875652214668596887984201319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97581417616714175943/25000000000000000000)
  centralHi := (390325670466856703773/100000000000000000000)
  directionLo := (39351205534004771129/10000000000000000000)
  directionHi := (393512055340047711291/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree063.table
  base := (-686208187113950358911692332151878178567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-379491471052378393939096513444608000000000000)
      constant := (5756010857356806033383870251810308891089315485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree063.table
  base := (-3431127707516931799060470957259959913347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-18645579844523877901054042328125917000000000000)
      constant := (283587045196032117822468114420665776196590585773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39351205534004771129/10000000000000000000)
  centralHi := (393512055340047711291/100000000000000000000)
  directionLo := (396672845516927630917/100000000000000000000)
  directionHi := (198336422758463815459/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree064.table
  base := (-150505844292405910997163505033833479741/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-385519140535539841831923736197588000000000000)
      constant := (5945308954135648002662877948648525215782338620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree064.table
  base := (-120407680391132444186270010137412946293/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-928145122848596359785244923928672788000000000000)
      constant := (14352689586470252524128964748247455314339458009075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396672845516927630917/100000000000000000000)
  centralHi := (198336422758463815459/50000000000000000000)
  directionLo := (399808648034336413531/100000000000000000000)
  directionHi := (99952162008584103383/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree065.table
  base := (-1283402307461837397831899661330769853629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-391546810018701289724750958950568000000000000)
      constant := (6137738325045607705188128183384247572894409478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree065.table
  base := (-2566869647708270784521447966206846455499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-942656833315522702418841773779175643000000000000)
      constant := (14817170225313863204005456190278143465237203991509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399808648034336413531/100000000000000000000)
  centralHi := (99952162008584103383/25000000000000000000)
  directionLo := (80584009261289911323/20000000000000000000)
  directionHi := (50365005788306194577/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree066.table
  base := (-52527842512652902532928594772415891427/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-397574479501862737617578181703548000000000000)
      constant := (6333298879970014624660191894203981555102534280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree066.table
  base := (-84046799673613307490591261956311342489/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-957168543782449045052438623629678498000000000000)
      constant := (15289206919446598686046761872724478836875722964975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80584009261289911323/20000000000000000000)
  centralHi := (50365005788306194577/12500000000000000000)
  directionLo := (406007601392066323263/100000000000000000000)
  directionHi := (6343868771751036301/1562500000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree067.table
  base := (-201631536587658215332041623858586995457/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-403602148985024185510405404456528000000000000)
      constant := (6531990542224523066960718826678782439677960696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree067.table
  base := (-1613101012550174240542483007644677899369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-971680254249375387686035473480181353000000000000)
      constant := (15768799488809630308103614304934920463148253826679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406007601392066323263/100000000000000000000)
  centralHi := (6343868771751036301/1562500000000000000)
  directionLo := (25566990823487752411/6250000000000000000)
  directionHi := (409071853175804038577/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree068.table
  base := (-551313664134826322333536182315168191563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-409629818468185633403232627209508000000000000)
      constant := (6733813246541153214869978478304377164971167466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree068.table
  base := (-1102669490695011250615579908244345064469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-986191964716301730319632323330684208000000000000)
      constant := (16255947780216551680181828356820626660449475240779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25566990823487752411/6250000000000000000)
  centralHi := (409071853175804038577/100000000000000000000)
  directionLo := (82422664294048184457/20000000000000000000)
  directionHi := (206056660735120461143/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree069.table
  base := (-142461178109769370037667559487096323751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-415657487951347081296059849962488000000000000)
      constant := (6938766937357616692422123339043625642759307364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree069.table
  base := (-569881196281829923055672594223980289447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1000703675183228072953229173181187063000000000000)
      constant := (16750651663317083046848460154876797379640280217977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82422664294048184457/20000000000000000000)
  centralHi := (206056660735120461143/50000000000000000000)
  directionLo := (207566253522689532099/50000000000000000000)
  directionHi := (415132507045379064199/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree070.table
  base := (-7354736619719784858214067103771058601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-421685157434508529188887072715468000000000000)
      constant := (7146851567365180176721360490863001236219246382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree070.table
  base := (-7370520035406999620720479350984448971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-20718681339799069705853592306769182000000000000)
      constant := (352100225044330548986946332025099513057323922378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207566253522689532099/50000000000000000000)
  centralHi := (415132507045379064199/100000000000000000000)
  directionLo := (418129892591200969279/100000000000000000000)
  directionHi := (1306655914347503029/312500000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree071.table
  base := (35173381715180994798837959125494106359/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-427712826917669977081714295468448000000000000)
      constant := (7358067096275574857884531327497606384747709296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree071.table
  base := (140686699435668540284646385817063762207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1029727096117080758220422872882192773000000000000)
      constant := (17762725777347062187891573893763985716597368787452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418129892591200969279/100000000000000000000)
  centralHi := (1306655914347503029/312500000000000000)
  directionLo := (105276485904639699149/25000000000000000000)
  directionHi := (421105943618558796597/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree072.table
  base := (581301191271687550312234201706148255871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-433740496400831424974541518221428000000000000)
      constant := (7572413489773570348466774726323962297878980478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree072.table
  base := (232515751653335528719810883737161699951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1044238806584007100854019722732695628000000000000)
      constant := (18280095833442718680759320199941570723990241702795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105276485904639699149/25000000000000000000)
  centralHi := (421105943618558796597/100000000000000000000)
  directionLo := (53007638662894671069/12500000000000000000)
  directionHi := (424061109303157368553/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree073.table
  base := (223096530653724240471784762913121108077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-439768165883992872867368740974408000000000000)
      constant := (7789890718626982440486006657863470452047171944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree073.table
  base := (892375905556127039230770531337987411289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1058750517050933443487616572583198483000000000000)
      constant := (18805021126999622508389722570408084994675633001202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53007638662894671069/12500000000000000000)
  centralHi := (424061109303157368553/100000000000000000000)
  directionLo := (106748955819240903523/25000000000000000000)
  directionHi := (426995823276963614093/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree074.table
  base := (1214640524253213279586962237486680659013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-445795835367154320760195963727388000000000000)
      constant := (8010498757930228349635448637383696356641306634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree074.table
  base := (1214631687775485295744363395913433234731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1073262227517859786121213422433701338000000000000)
      constant := (19337501599716514417164989870650702426353414267158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106748955819240903523/25000000000000000000)
  centralHi := (426995823276963614093/100000000000000000000)
  directionLo := (429910504370990570709/100000000000000000000)
  directionHi := (42991050437099057071/10000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree075.table
  base := (1548063268431356746679926793183153581001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-451823504850315768653023186480368000000000000)
      constant := (8234237586461209221452922085937970584087276818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree075.table
  base := (3096111253512159944699435720640238118839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1087773937984786128754810272284204193000000000000)
      constant := (19877537201936760180875884214409549189479834918551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429910504370990570709/100000000000000000000)
  centralHi := (42991050437099057071/10000000000000000000)
  directionLo := (432805557313058381493/100000000000000000000)
  directionHi := (216402778656529190747/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree076.table
  base := (3785306788146486869897144848240665631657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-457851174333477216545850409233348000000000000)
      constant := (8461107186134395308577230835702104422928260713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree076.table
  base := (3785293572626791354865996871841289979501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1102285648451712471388407122134707048000000000000)
      constant := (20425127891361654173777232237587971486498516906509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432805557313058381493/100000000000000000000)
  centralHi := (216402778656529190747/50000000000000000000)
  directionLo := (435681373383823495649/100000000000000000000)
  directionHi := (8713627467676469913/2000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree077.table
  base := (4496820164119672878112621547336564341171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-463878843816638664438677631986328000000000000)
      constant := (8691107541535604574523750966981035733886077939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree077.table
  base := (4496808737799263291091518405996296148039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-22791782835074261510653142285412447000000000000)
      constant := (428168849631762802159676091399373376747388048599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435681373383823495649/100000000000000000000)
  centralHi := (8713627467676469913/2000000000000000000)
  directionLo := (219269165517043335797/50000000000000000000)
  directionHi := (87707666206817334319/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree078.table
  base := (326916579274335733820050238012975102353/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-469906513299800112331504854739308000000000000)
      constant := (8924238639526176225291766999626689323808630032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree078.table
  base := (5230655390020332677129608497481945095077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1131309069385565156655600821835712758000000000000)
      constant := (21542974393019539535597903013403338450480390362693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219269165517043335797/50000000000000000000)
  centralHi := (87707666206817334319/20000000000000000000)
  directionLo := (220688398233068510567/50000000000000000000)
  directionHi := (88275359293227404227/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree079.table
  base := (5986840910605929106626226839586530185529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-475934182782961560224332077492288000000000000)
      constant := (9160500468906110363080530905418031662515642361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree079.table
  base := (5986832371330451008327454013028606296721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1145820779852491499289197671686215613000000000000)
      constant := (22113230148391666281194007598721088033481680781489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220688398233068510567/50000000000000000000)
  centralHi := (88275359293227404227/20000000000000000000)
  directionLo := (444197124181660260817/100000000000000000000)
  directionHi := (222098562090830130409/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree080.table
  base := (6765346075987753009217493137451260981253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-481961852266123008117159300245268000000000000)
      constant := (9399893020127326989087486845239718914572609477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree080.table
  base := (3382669347504303307979226189750228565639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1160332490319417841922794521536718468000000000000)
      constant := (22691040875781734287515134537253409682556815479502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444197124181660260817/100000000000000000000)
  centralHi := (222098562090830130409/50000000000000000000)
  directionLo := (446999657498531946783/100000000000000000000)
  directionHi := (13968739296829123337/3125000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree081.table
  base := (1513235979874993840442515168724282559051/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-487989521749284456009986522998248000000000000)
      constant := (9642416285049536846525603628383131872990554295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree081.table
  base := (7566173520202100291158266247568975960151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1174844200786344184556391371387221323000000000000)
      constant := (23276406556194032659059536704162586621411554882359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446999657498531946783/100000000000000000000)
  centralHi := (13968739296829123337/3125000000000000000)
  directionLo := (449784729038628465223/100000000000000000000)
  directionHi := (56223091129828558153/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree082.table
  base := (4194670821567279389916297255022792429357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-494017191232445903902813745751228000000000000)
      constant := (9888070256732350860510407768712554907935640026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree082.table
  base := (8389336130331484062537789035630560654089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1189355911253270527189988221237724178000000000000)
      constant := (23869327173440308637490531050161652639911570485801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449784729038628465223/100000000000000000000)
  centralHi := (56223091129828558153/12500000000000000000)
  directionLo := (452552661188617903559/100000000000000000000)
  directionHi := (11313816529715447589/2500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree083.table
  base := (9234830678341765246723934109083714428133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-500044860715607351795640968504208000000000000)
      constant := (10136854929258215997177117102432922669054303397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree083.table
  base := (9234825914705515796599190659447685262637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1203867621720196869823585071088227033000000000000)
      constant := (24469802713724430875549088894337127031172399830733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452552661188617903559/100000000000000000000)
  centralHi := (11313816529715447589/2500000000000000000)
  directionLo := (91060753307107568693/20000000000000000000)
  directionHi := (227651883267768921733/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree084.table
  base := (78926925537102661741323769340069687463/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-506072530198768799688468191257188000000000000)
      constant := (10388770297581580019234658424821803608235438976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree084.table
  base := (10102642352866243030304007145856493079903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-24864884330349453315452692264055712000000000000)
      constant := (511792513577321001735125227137246721426051559023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91060753307107568693/20000000000000000000)
  centralHi := (227651883267768921733/50000000000000000000)
  directionLo := (45803834827882600671/10000000000000000000)
  directionHi := (458038348278826006711/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree085.table
  base := (10992788557128022682633029829343621556563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-512100199681930247581295414010168000000000000)
      constant := (10643816357400378441543297227138824135225701267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree085.table
  base := (10992785001256602343676127295709046342399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1232891042654049555090778770789232743000000000000)
      constant := (25693418518112801654172421648440587741677552890591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45803834827882600671/10000000000000000000)
  centralHi := (458038348278826006711/100000000000000000000)
  directionLo := (460756700620341138311/100000000000000000000)
  directionHi := (57594587577542642289/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree086.table
  base := (11905256553629518848070173129067077816419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-518127869165091695474122636763148000000000000)
      constant := (10901993105046523036095878032086880135174686371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree086.table
  base := (2976313370466051899336914576975557829691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1247402753120975897724375620639735598000000000000)
      constant := (26316558763656967365617010129902866554342279392876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460756700620341138311/100000000000000000000)
  centralHi := (57594587577542642289/12500000000000000000)
  directionLo := (463459109133794275837/100000000000000000000)
  directionHi := (231729554566897137919/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree087.table
  base := (1284005012586493476433849689272880781989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-524155538648253143366949859516128000000000000)
      constant := (11163300537392568576954780748756111352777345010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree087.table
  base := (1605005934068373812074766704251676925951/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1261914463587902240357972470490238453000000000000)
      constant := (26947253894643711855230256861832311158969010996472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463459109133794275837/100000000000000000000)
  centralHi := (231729554566897137919/50000000000000000000)
  directionLo := (14567057847340734811/3125000000000000000)
  directionHi := (466145851114903513953/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree088.table
  base := (344929224761261329654179778902798758747/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-530183208131414591259777082269108000000000000)
      constant := (11427738651772156727659252326193201340842020920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree088.table
  base := (1724645837348809496207545040089755484549/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1276426174054828582991569320340741308000000000000)
      constant := (27585503904871476146035593542315629959673966559528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14567057847340734811/3125000000000000000)
  centralHi := (466145851114903513953/100000000000000000000)
  directionLo := (18752687836539501441/4000000000000000000)
  directionHi := (234408597956743768013/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree089.table
  base := (14776612905798980717220456683432920617/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-536210877614576039152604305022088000000000000)
      constant := (11695307445912194526443169229388662350085353000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree089.table
  base := (14776610926683926983272107145970540335477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1290937884521754925625166170191244163000000000000)
      constant := (28231308789055980672517959806455510341828623926293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18752687836539501441/4000000000000000000)
  centralHi := (234408597956743768013/50000000000000000000)
  directionLo := (235736702624311831667/50000000000000000000)
  directionHi := (94294681049724732667/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree090.table
  base := (3944595416493612476112333987477242637333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-542238547097737487045431527775068000000000000)
      constant := (11966006917875029514640793816991813503898664788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree090.table
  base := (15778379956934396293046813020326013354183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1305449594988681268258763020041747018000000000000)
      constant := (28884668542694996669842893653201252958118468340647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235736702624311831667/50000000000000000000)
  centralHi := (94294681049724732667/20000000000000000000)
  directionLo := (14816085422122317967/3125000000000000000)
  directionHi := (94822946701582834989/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree091.table
  base := (8401237547725686710192532523742361556031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-548266216580898934938258750528048000000000000)
      constant := (12239837066009142381987972489391761759761391358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree091.table
  base := (16802473619764736628609280589610564566589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-26937985825624645120252242242698977000000000000)
      constant := (602971084937818103592469868688733450673344759149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14816085422122317967/3125000000000000000)
  centralHi := (94822946701582834989/20000000000000000000)
  directionLo := (29796339251989341811/6250000000000000000)
  directionHi := (476741428031829468977/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree092.table
  base := (17848893044645829536446969921113256641207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-554293886064060382831085973281028000000000000)
      constant := (12516797888907098008940489684404570631737116663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree092.table
  base := (17848891770564573741541367353533991944163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1334473015922533953525956719742752728000000000000)
      constant := (30214052643563357624942967051108230259816513830467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29796339251989341811/6250000000000000000)
  centralHi := (476741428031829468977/100000000000000000000)
  directionLo := (95870745876805526777/20000000000000000000)
  directionHi := (239676864692013816943/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree093.table
  base := (945881769305196951435243963413161518419/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-560321555547221830723913196034008000000000000)
      constant := (12796889385369682845880386420244722734536087420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree093.table
  base := (295588035721605539488596776263829521247/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1348984726389460296159553569593255583000000000000)
      constant := (30890076984743699508432940244377517450068226766272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95870745876805526777/20000000000000000000)
  centralHi := (239676864692013816943/50000000000000000000)
  directionLo := (240975935804243303429/50000000000000000000)
  directionHi := (481951871608486606859/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree094.table
  base := (20008702011250801866951238935605153334329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-566349225030383278616740418786988000000000000)
      constant := (13080111554375315658423439819883540887722701561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree094.table
  base := (2501087632720795820107080973996371794217/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1363496436856386638793150419443758438000000000000)
      constant := (31573656183125379638232931846888752728864019159624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240975935804243303429/50000000000000000000)
  centralHi := (481951871608486606859/100000000000000000000)
  directionLo := (484536082474226804123/100000000000000000000)
  directionHi := (121134020618556701031/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree095.table
  base := (422441856552344913397561409920003673027/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-572376894513544726509567641539968000000000000)
      constant := (13366464395053954003633923114300075727975552150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree095.table
  base := (21122092008065527584511485502066524187517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1378008147323312981426747269294261293000000000000)
      constant := (32264790236692153121008284723161613185893914234653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484536082474226804123/100000000000000000000)
  centralHi := (121134020618556701031/25000000000000000000)
  directionLo := (60888322963543556861/12500000000000000000)
  directionHi := (487106583708348454889/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree096.table
  base := (11128903878236988432726472878737083035773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-578404563996706174402394864292948000000000000)
      constant := (13655947906664833958292583186636042428567176314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree096.table
  base := (44515614098270276128082712288803244601/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1392519857790239324060344119144764148000000000000)
      constant := (32963479143728343529676141080542939117005196204500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60888322963543556861/12500000000000000000)
  centralHi := (487106583708348454889/100000000000000000000)
  directionLo := (244831795609029221333/50000000000000000000)
  directionHi := (489663591218058442667/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree097.table
  base := (4683169346162628390222990884883202080583/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (166)
      previous := (83)
      next := (83)
      square := (661073643689564366399125110000000000000)
      linear := (-62114170844921630597855466792000000000000)
      constant := (1482470197531882094674654525658416010402915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree097.table
  base := (11707923060187497103806078221097629882099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (398566)
      previous := (199283)
      next := (199283)
      square := (1587237818498644043724299389110000000000000)
      linear := (-149541031805416693239870439897467000000000000)
      constant := (3578459230818850789560351000680204193693839398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244831795609029221333/50000000000000000000)
  centralHi := (489663591218058442667/100000000000000000000)
  directionLo := (98441463060463176369/20000000000000000000)
  directionHi := (246103657651157940923/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree098.table
  base := (12298104846813086763762916161715489904081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-590459902963029070188049309798908000000000000)
      constant := (14244306940255494404477273122544586089014996258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree098.table
  base := (196769673334866735303199120591028572749/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-592063006548976263776567188190658000000000000)
      constant := (14320500421736765086477926220706534980124417625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98441463060463176369/20000000000000000000)
  centralHi := (246103657651157940923/50000000000000000000)
  directionLo := (123684490213420899161/25000000000000000000)
  directionHi := (98947592170736719329/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree099.table
  base := (25798896596434345848300281682398815121619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-596487572446190518080876532551888000000000000)
      constant := (14543182461242744954795189991771812451479313171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree099.table
  base := (25798896141906342271447653612417474514259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1436054989191018351961134668696272713000000000000)
      constant := (35104874972120039140766115870659728984883895697331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123684490213420899161/25000000000000000000)
  centralHi := (98947592170736719329/20000000000000000000)
  directionLo := (15539241485966681877/3125000000000000000)
  directionHi := (99451145510186764013/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree100.table
  base := (1688994212377180901330176232105370529381/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-602515241929351965973703755304868000000000000)
      constant := (14845188651151553468640884102052870900975133264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree100.table
  base := (27023907005872210254640192704143865665031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1450566699657944694594731518546775568000000000000)
      constant := (35833783280469104705968675140989051456533506306279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15539241485966681877/3125000000000000000)
  centralHi := (99451145510186764013/20000000000000000000)
  directionLo := (249880405021460258457/50000000000000000000)
  directionHi := (99952162008584103383/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree101.table
  base := (28271242063431030964722556928172141729071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-608542911412513413866530978057848000000000000)
      constant := (15150325509652635165071361334184629681528829039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree101.table
  base := (7067810431276036127486053242230829594123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1465078410124871037228328368397278423000000000000)
      constant := (36570246436876941521019886840763091648128196160428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249880405021460258457/50000000000000000000)
  centralHi := (99952162008584103383/20000000000000000000)
  directionLo := (100450679624839501719/20000000000000000000)
  directionHi := (125563349531049377149/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree102.table
  base := (14770450281459425424798226777313671330201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-614570580895674861759358200810828000000000000)
      constant := (15458593036466506005432143906959584667091722418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree102.table
  base := (1477045013553036374163491565999373694213/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1479590120591797379861925218247781278000000000000)
      constant := (37314264440698770165082548434359717785906582618340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100450679624839501719/20000000000000000000)
  centralHi := (125563349531049377149/25000000000000000000)
  directionLo := (504733676902830812379/100000000000000000000)
  directionHi := (25236683845141540619/5000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree103.table
  base := (3854110358913513223917519019832062153701/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-620598250378836309652185423563808000000000000)
      constant := (15769991231356150943613765781277512982433381672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree103.table
  base := (30832882619556360002176051922902839676853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1494101831058723722495522068098284133000000000000)
      constant := (38065837291388213549581652832914280330640343214677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504733676902830812379/100000000000000000000)
  centralHi := (25236683845141540619/5000000000000000000)
  directionLo := (507201826960825099843/100000000000000000000)
  directionHi := (126800456740206274961/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree104.table
  base := (32147188967257202628335539622473204021507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-626625919861997757545012646316788000000000000)
      constant := (16084520094120766929558562130813162376638359363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree104.table
  base := (1607359437505880191122513516035908534637/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1508613541525650065129118917948786988000000000000)
      constant := (38824964988482756046881248891226353592583225574660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507201826960825099843/100000000000000000000)
  centralHi := (126800456740206274961/25000000000000000000)
  directionLo := (254829012253778871009/50000000000000000000)
  directionHi := (509658024507557742019/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree105.table
  base := (16741909416352838405978551415211006701371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-632653589345159205437839869069768000000000000)
      constant := (16402179624590423052328515502661330724106399478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree105.table
  base := (8370954661358531286668275358140067882309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-31084188816175028729851342199985507000000000000)
      constant := (807992806767170198987159818452233989521110494676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254829012253778871009/50000000000000000000)
  centralHi := (509658024507557742019/100000000000000000000)
  directionLo := (256051220763294686947/50000000000000000000)
  directionHi := (102420488305317874779/20000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree106.table
  base := (17421386226194925479354815850344220726997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-638681258828320653330667091822748000000000000)
      constant := (16722969822621503371422319465162225545640629546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree106.table
  base := (17421386145445167309126800349184587586337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1537636962459502750396312617649792698000000000000)
      constant := (40365884920383783749355349233838800257148454888066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256051220763294686947/50000000000000000000)
  centralHi := (102420488305317874779/20000000000000000000)
  directionLo := (51453524591619712449/10000000000000000000)
  directionHi := (514535245916197124491/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree107.table
  base := (18112024906714743811902666954055682777517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-644708928311482101223494314575728000000000000)
      constant := (17046890688092817732721965680328405838507314906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree107.table
  base := (7244809934833173345783204241860042017719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1552148672926429093029909467500295553000000000000)
      constant := (41147677154581758555754056307364925750188340442355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51453524591619712449/10000000000000000000)
  centralHi := (514535245916197124491/100000000000000000000)
  directionLo := (51695660162395548087/10000000000000000000)
  directionHi := (516956601623955480871/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree108.table
  base := (37627650904975035079041263133392102554777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-650736597794643549116321537328708000000000000)
      constant := (17373942220902282704016792626241590292937896793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree108.table
  base := (37627650784894786646195603960938265969503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1566660383393355435663506317350798408000000000000)
      constant := (41937024233951087242473327461886269168961435998527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51695660162395548087/10000000000000000000)
  centralHi := (516956601623955480871/100000000000000000000)
  directionLo := (8115104199619844653/1562500000000000000)
  directionHi := (519366668775670057793/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree109.table
  base := (39053575717906591048166831246746510835611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-656764267277804997009148760081688000000000000)
      constant := (17704124420964089124789558519188639920452263899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree109.table
  base := (39053575614374900001426205452693592967229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1581172093860281778297103167201301263000000000000)
      constant := (42733926158295178458210876531585715969340007044061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8115104199619844653/1562500000000000000)
  centralHi := (519366668775670057793/100000000000000000000)
  directionLo := (521765603798951212749/100000000000000000000)
  directionHi := (2087062415195804851/400000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree110.table
  base := (40501824244577011002111651333176058532673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-662791936760966444901975982834668000000000000)
      constant := (18037437288206285012166240088686333534733920257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree110.table
  base := (40501824155319809327624034827530877600061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1595683804327208120930700017051804118000000000000)
      constant := (43538382927449425132212495494357863671140876451549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521765603798951212749/100000000000000000000)
  centralHi := (2087062415195804851/400000000000000000)
  directionLo := (104830711908339474571/20000000000000000000)
  directionHi := (65519194942712171607/12500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree111.table
  base := (10493099119648174473600436149450497029/2500000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-668819606244127892794803205587648000000000000)
      constant := (18373880822568713011536563668253656906183444000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree111.table
  base := (41972396401647442071073921221525057483993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1610195514794134463564296866902306973000000000000)
      constant := (44350394541276427108678551941779243414721403218937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104830711908339474571/20000000000000000000)
  centralHi := (65519194942712171607/12500000000000000000)
  directionLo := (52653068538574202827/10000000000000000000)
  directionHi := (526530685385742028271/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree112.table
  base := (10866323103656639338981809405259921982789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-674847275727289340687630428340628000000000000)
      constant := (18713455024001250491981574458885738423744246804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree112.table
  base := (5433161543537462132803000407803718500331/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-33157290311450220534650892178628772000000000000)
      constant := (921835938768610546501414437743320097448888836568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52653068538574202827/10000000000000000000)
  centralHi := (526530685385742028271/100000000000000000000)
  directionLo := (52889712735590350789/10000000000000000000)
  directionHi := (528897127355903507891/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree113.table
  base := (44980512048258410416253524438456272440357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-680874945210450788580457651093608000000000000)
      constant := (19056159892462307989568453253063229067391319013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree113.table
  base := (1405640999721520079961078814581050356039/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1639218935727987148831490566603312683000000000000)
      constant := (45997082302511284538189076058069790427702368107232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52889712735590350789/10000000000000000000)
  centralHi := (528897127355903507891/100000000000000000000)
  directionLo := (531253028224662805637/100000000000000000000)
  directionHi := (265626514112331402819/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree114.table
  base := (46518055375838845264049399567668763402731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-686902614693612236473284873846588000000000000)
      constant := (19401995427917548188564384738402387394856295979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree114.table
  base := (46518055326565369500845983743640220474467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1653730646194913491465087416453815538000000000000)
      constant := (46831758449746616051940848648267621493000668267203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531253028224662805637/100000000000000000000)
  centralHi := (265626514112331402819/50000000000000000000)
  directionLo := (533598527612681795379/100000000000000000000)
  directionHi := (26679926380634089769/5000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree115.table
  base := (9615584478874615571984152119557451132039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-692930284176773684366112096599568000000000000)
      constant := (19750961630338793165942709805319150288506774755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree115.table
  base := (24038961175954087770831642941928903054359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1668242356661839834098684266304318393000000000000)
      constant := (47673989441304166216707434098162457706897303316462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533598527612681795379/100000000000000000000)
  centralHi := (26679926380634089769/5000000000000000000)
  directionLo := (133983440521340522787/25000000000000000000)
  directionHi := (535933762085362091149/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree116.table
  base := (49660113101421893249315783610622556561763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-698957953659935132258939319352548000000000000)
      constant := (20103058499703092348196050342567275634689628067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree116.table
  base := (1551878533275851351129407300643568537203/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1682754067128766176732281116154821248000000000000)
      constant := (48523775277132205745979003066733205981714233850464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133983440521340522787/25000000000000000000)
  centralHi := (535933762085362091149/100000000000000000000)
  directionLo := (6728235815570418927/1250000000000000000)
  directionHi := (538258865245633514161/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree117.table
  base := (51264627495017167872973580244560684193291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-704985623143096580151766542105528000000000000)
      constant := (20458286035991927660755320651552337477574675019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree117.table
  base := (51264627463483391929653588443503118548409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1697265777595692519365877966005324103000000000000)
      constant := (49381115957189185693034281862761887293030174654681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6728235815570418927/1250000000000000000)
  centralHi := (538258865245633514161/100000000000000000000)
  directionLo := (540573967823150561839/100000000000000000000)
  directionHi := (6757174597789382023/1250000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree118.table
  base := (52891465573589838848660807646312612935223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-711013292626258028044593764858508000000000000)
      constant := (20816644239190535790961587209367739375107513207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree118.table
  base := (52891465546418837901753027026341372976933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1711777488062618861999474815855826958000000000000)
      constant := (50246011481442173252724577966354031365494250195397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540573967823150561839/100000000000000000000)
  centralHi := (6757174597789382023/1250000000000000000)
  directionLo := (8482487465001021619/1562500000000000000)
  directionHi := (542879197760065383617/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree119.table
  base := (2181625093436339932727715465420703040779/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-717040962109419475937420987611488000000000000)
      constant := (21178133109287330422277191310505466872767240275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree119.table
  base := (54540627312498200211396287279652795020649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-35230391806725412339450442157272037000000000000)
      constant := (1043233915303377939265150185560391331644115035609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8482487465001021619/1562500000000000000)
  centralHi := (542879197760065383617/100000000000000000000)
  directionLo := (109034936058707301041/20000000000000000000)
  directionHi := (272587340146768252603/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree120.table
  base := (2248484511241082295113826195857552457987/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-723068631592580923830248210364468000000000000)
      constant := (21542752646273409804206992311736752776929992075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree120.table
  base := (3513257047553640507490884608775996060739/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1740800908996471547266668515556832668000000000000)
      constant := (51998467062439721753449916885989262255873908730416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109034936058707301041/20000000000000000000)
  centralHi := (272587340146768252603/50000000000000000000)
  directionLo := (547460538035123862679/100000000000000000000)
  directionHi := (13686513450878096567/2500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree121.table
  base := (28952960954120075770624085347145780853937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-729096301075742371723075433117448000000000000)
      constant := (21910502850142137162298726022279007304109386466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree121.table
  base := (28952960945432553238004799566640032409779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1755312619463397889900265365407335523000000000000)
      constant := (52886027119150461561853490223713598471234218154022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547460538035123862679/100000000000000000000)
  centralHi := (13686513450878096567/2500000000000000000)
  directionLo := (274868445523606284303/50000000000000000000)
  directionHi := (549736891047212568607/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree122.table
  base := (149055136792612884596990026824977259323/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-735123970558903819615902655870428000000000000)
      constant := (22281383720888783279395384423311140413188042800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree122.table
  base := (59622054702077823609945897907384501457037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1769824329930324232533862215257838378000000000000)
      constant := (53781142019987776906059425329462160382376435980333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274868445523606284303/50000000000000000000)
  centralHi := (549736891047212568607/100000000000000000000)
  directionLo := (552003856916600197057/100000000000000000000)
  directionHi := (276001928458300098529/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree123.table
  base := (6136051120710982741324069365270808901861/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-741151640042065267508729878623408000000000000)
      constant := (22655395258510222138907116553803204409576101490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree123.table
  base := (61360511194217366847317920644633837068297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1784336040397250575167459065108341233000000000000)
      constant := (54683811764945364156410297315444589823289431141673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552003856916600197057/100000000000000000000)
  centralHi := (276001928458300098529/50000000000000000000)
  directionLo := (22170462033015008289/4000000000000000000)
  directionHi := (277130775412687603613/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree124.table
  base := (63121291378244790987674006007988958492631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-747179309525226715401557101376388000000000000)
      constant := (23032537463004671852399493033362240110457165079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree124.table
  base := (31560645683570123890878609380435210488407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1798847750864176917801055914958844088000000000000)
      constant := (55594036354019981765026440902380144050120993865326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22170462033015008289/4000000000000000000)
  centralHi := (277130775412687603613/50000000000000000000)
  directionLo := (22260403424768295781/4000000000000000000)
  directionHi := (278255042809603697263/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree125.table
  base := (64904395230380091409081271646251869632963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-753206979008388163294384324129368000000000000)
      constant := (23412810334371474230655798774096833841376548867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree125.table
  base := (12980879044163219276340822995461714550929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1813359461331103260434652764809346943000000000000)
      constant := (56511815787210943642251561136826680247252339986805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22260403424768295781/4000000000000000000)
  centralHi := (278255042809603697263/50000000000000000000)
  directionLo := (558749571873164933479/100000000000000000000)
  directionHi := (13968739296829123337/2500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree126.table
  base := (16677455690886320159139943698646567565797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-759234648491549611187211546882348000000000000)
      constant := (23796213872610907328059180123299670216906335892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree126.table
  base := (66709822755308602809340055788144601666081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-37303493302000604144249992135915302000000000000)
      constant := (1172186736010605890063524704819747054796731650321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558749571873164933479/100000000000000000000)
  centralHi := (13968739296829123337/2500000000000000000)
  directionLo := (560980117955166630873/100000000000000000000)
  directionHi := (280490058977583315437/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree127.table
  base := (6853757397785248263255039229794666569251/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-765262317974711059080038769635328000000000000)
      constant := (24182748077724026118972243291204926177500826590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree127.table
  base := (68537573970759331007011172690922804923657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1842382882264955945701846464510352653000000000000)
      constant := (58370039185949414749905506038179127059710579599913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560980117955166630873/100000000000000000000)
  centralHi := (280490058977583315437/50000000000000000000)
  directionLo := (70400228760896551889/12500000000000000000)
  directionHi := (563201830087172415113/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree128.table
  base := (70387648873482010833496557120204858851773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-771289987457872506972865992388308000000000000)
      constant := (24572412949712527172518484538569671516936332157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree128.table
  base := (35193824433686990402723238912690349479309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1856894592731882288335443314360855508000000000000)
      constant := (59310483151504769019357245232671163862600429865562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70400228760896551889/12500000000000000000)
  centralHi := (563201830087172415113/100000000000000000000)
  directionLo := (17669212887631557023/3125000000000000000)
  directionHi := (565414812404209824737/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree129.table
  base := (72260047450670161105520526831963138982227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-777317656941033954865693215141288000000000000)
      constant := (24965208488578633796502248186875703174683773843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree129.table
  base := (36130023722705368678923695025759037158407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1871406303198808630969040164211358363000000000000)
      constant := (60258481961191584084587567751922741101928813925326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669212887631557023/3125000000000000000)
  centralHi := (565414812404209824737/100000000000000000000)
  directionLo := (567619167011329303943/100000000000000000000)
  directionHi := (70952395876416162993/12500000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree130.table
  base := (18538692427424714984393678421653092992353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-783345326424195402758520437894268000000000000)
      constant := (25361134694324998637258087483015175807860197508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree130.table
  base := (593238157641363197324284892950189336763/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1885918013665734973602637014061861218000000000000)
      constant := (61214035615016655298542523183346249509814620483375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567619167011329303943/100000000000000000000)
  centralHi := (70952395876416162993/12500000000000000000)
  directionLo := (569814994038576445373/100000000000000000000)
  directionHi := (284907497019288222687/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree131.table
  base := (38035907825443447230216663306616584504263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-789372995907356850651347660647248000000000000)
      constant := (25760191566954621162899456958801808887201221134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree131.table
  base := (38035907823494012583063444957899937853479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1900429724132661316236233863912364073000000000000)
      constant := (62177144112987551946810805814740461916669769540622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569814994038576445373/100000000000000000000)
  centralHi := (284907497019288222687/50000000000000000000)
  directionLo := (572002391694064921613/100000000000000000000)
  directionHi := (286001195847032460807/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree132.table
  base := (78011185274582490875467357853170502088303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-795400665390518298544174883400228000000000000)
      constant := (26162379106470777833755056280234417254148842927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree132.table
  base := (78011185271225865940546770892776181609297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1914941434599587658869830713762866928000000000000)
      constant := (63147807455112457669412873382995796539721263010673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (572002391694064921613/100000000000000000000)
  centralHi := (286001195847032460807/50000000000000000000)
  directionLo := (574181456315229699417/100000000000000000000)
  directionHi := (287090728157614849709/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree133.table
  base := (79972878581157042031745481073734016535531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-801428334873679746437002106153208000000000000)
      constant := (26567697312876963085141772597848717361582811179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree133.table
  base := (39986439289133702515159705820598489171151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-39376594797275795949049542114558567000000000000)
      constant := (1308694400844898688473288683564971776466913256382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (574181456315229699417/100000000000000000000)
  centralHi := (287090728157614849709/50000000000000000000)
  directionLo := (144088070604584054623/25000000000000000000)
  directionHi := (576352282418336218493/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree134.table
  base := (16391379114199962811361043427775943408771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-807456004356841194329829328906188000000000000)
      constant := (26976146186176839522053606445453671257665631695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree134.table
  base := (81956895568512329468939357947612863858691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1943964855533440344137024413463872638000000000000)
      constant := (65111798671859315477516480735118800075447463109219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144088070604584054623/25000000000000000000)
  centralHi := (576352282418336218493/100000000000000000000)
  directionLo := (578514962746317524633/100000000000000000000)
  directionHi := (289257481373158762317/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree135.table
  base := (2623851132641046464183460488367193641993/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-813483673840002642222656551659168000000000000)
      constant := (27387725726374195959699994034619431599280388384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree135.table
  base := (41981618121186150313482594843542799785177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1958476566000366686770621263314375493000000000000)
      constant := (66105126546499596742116120317286084753039263347186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578514962746317524633/100000000000000000000)
  centralHi := (289257481373158762317/50000000000000000000)
  directionLo := (58066958831500786133/10000000000000000000)
  directionHi := (580669588315007861331/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree136.table
  base := (42995950301055202274151336116691651136683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-819511343323164090115483774412148000000000000)
      constant := (27802435933472912143956453586581791491090100694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree136.table
  base := (10748987575033425369055097073613238969407/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1972988276467293029404218113164878348000000000000)
      constant := (67106009265330369660536583334634705440616194093304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58066958831500786133/10000000000000000000)
  centralHi := (580669588315007861331/100000000000000000000)
  directionLo := (58281624845783793149/10000000000000000000)
  directionHi := (582816248457837931491/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree137.table
  base := (8804288864420943012970751032680514691673/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-825539012806325538008310997165128000000000000)
      constant := (28220276807476929156692192503378735627339512570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree137.table
  base := (17608577728524633934147261878988089482021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-1987499986934219372037814963015381203000000000000)
      constant := (68114446828361247457702006794545888237280708745945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58281624845783793149/10000000000000000000)
  centralHi := (582816248457837931491/100000000000000000000)
  directionLo := (9139922357328967653/1562500000000000000)
  directionHi := (584955030869053929793/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree138.table
  base := (1408065630800520531982436426555930328187/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-831566682289486985901138219918108000000000000)
      constant := (28641248348390224656879882306223487901306334912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree138.table
  base := (45058100184934049464969479136219858620087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2002011697401145714671411812865884058000000000000)
      constant := (69130439235601910339132311291052520935630225995566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9139922357328967653/1562500000000000000)
  centralHi := (584955030869053929793/100000000000000000000)
  directionLo := (117417204329103900999/20000000000000000000)
  directionHi := (146771505411379876249/25000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree139.table
  base := (92211835783606499757790449778612605214229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-837594351772648433793965442671088000000000000)
      constant := (29065350556216792233015680475240608002460680661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree139.table
  base := (92211835782431586614246764249080439995543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2016523407868072057305008662716386913000000000000)
      constant := (70153986487062058791111977726793217538038271872887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117417204329103900999/20000000000000000000)
  centralHi := (146771505411379876249/25000000000000000000)
  directionLo := (589209305327157029951/100000000000000000000)
  directionHi := (9206395395736828593/1562500000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree140.table
  base := (3773191795270132021880848739137558715637/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-843622021255809881686792665424068000000000000)
      constant := (29492583430960624248794107577321152248885713325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree140.table
  base := (2947806090023194153696687985937559059651/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-41449696292550987753849092093201832000000000000)
      constant := (1452756909852068874952555327730014151325457814112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589209305327157029951/100000000000000000000)
  centralHi := (9206395395736828593/1562500000000000000)
  directionLo := (73915620617010240663/12500000000000000000)
  directionHi := (118264992987216385061/20000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree141.table
  base := (48235038833048195790155911278229578771743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-849649690738971329579619888177048000000000000)
      constant := (29922946972625697654849645005211102213326659774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree141.table
  base := (96470077665226329053000641544721021796291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2045546828801924742572202362417392623000000000000)
      constant := (72223745522679490287865064309651070418264206147619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73915620617010240663/12500000000000000000)
  centralHi := (118264992987216385061/20000000000000000000)
  directionLo := (593433082014481291831/100000000000000000000)
  directionHi := (74179135251810161479/12500000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree142.table
  base := (98632684137055569412215469154919920549073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-855677360222132777472447110930028000000000000)
      constant := (30356441181215962316964083884911857532446227857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree142.table
  base := (98632684136306898371466177627590555164759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2060058539268851085205799212267895478000000000000)
      constant := (73269957306855960205598079261423989383542067051831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593433082014481291831/100000000000000000000)
  centralHi := (74179135251810161479/12500000000000000000)
  directionLo := (4764269893290285981/800000000000000000)
  directionHi := (297766868330642873813/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree143.table
  base := (50408807147523369101623218024860860871093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-861705029705294225365274333683008000000000000)
      constant := (30793066056735331477383703056016865679872228074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree143.table
  base := (50408807147201276480292705176080854126031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2074570249735777427839396062118398333000000000000)
      constant := (74323723935290241947116984819173804863952706910558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4764269893290285981/800000000000000000)
  centralHi := (297766868330642873813/50000000000000000000)
  directionLo := (298813503783840565983/50000000000000000000)
  directionHi := (597627007567681131967/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree144.table
  base := (103024868140481087914073367282233087705137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-867732699188455673258101556435988000000000000)
      constant := (31232821599187674022448433790311363122217634033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree144.table
  base := (51512434069963416255149566815304130150117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2089081960202703770472992911968901188000000000000)
      constant := (75385045407991677791279090667637579915916928996106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298813503783840565983/50000000000000000000)
  centralHi := (597627007567681131967/100000000000000000000)
  directionLo := (599712972051504620297/100000000000000000000)
  directionHi := (299856486025752310149/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree145.table
  base := (52627222836882217438021379356016041406167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-873760368671617121150928779188968000000000000)
      constant := (31675707808576808278019915267338119867181250606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree145.table
  base := (52627222836643788596355231357877210212103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2103593670669630113106589761819404043000000000000)
      constant := (76453921724969481259082939832419903522968021563854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599712972051504620297/100000000000000000000)
  centralHi := (299856486025752310149/50000000000000000000)
  directionLo := (60179170609056778747/10000000000000000000)
  directionHi := (601791706090567787471/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree146.table
  base := (53753173447648349759052409931506363818103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-879788038154778569043756001941948000000000000)
      constant := (32121724684906497095414140008507454754329062254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree146.table
  base := (107506346894886450481483432502436098570579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2118105381136556455740186611669906898000000000000)
      constant := (77530352886232726333677047788806327780232837324211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60179170609056778747/10000000000000000000)
  centralHi := (601791706090567787471/100000000000000000000)
  directionLo := (301931642177473626377/50000000000000000000)
  directionHi := (120772656870989450551/20000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree147.table
  base := (13722571475683937471202712509609111650823/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-885815707637940016936583224694928000000000000)
      constant := (32570872228180444025728476476975403052180748856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree147.table
  base := (109780571805118571423677608123871813578473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-888220363016860807319360042282553000000000000)
      constant := (32742331899954327010832823238757800268959852457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301931642177473626377/50000000000000000000)
  centralHi := (120772656870989450551/20000000000000000000)
  directionLo := (605927780238281734091/100000000000000000000)
  directionHi := (151481945059570433523/25000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree148.table
  base := (5603856020233792092509169870128318692883/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-891843377121101464829410447447908000000000000)
      constant := (33023150438402290410483046964384571011626722940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree148.table
  base := (112077120404372238931683869375704603411011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2147128802070409141007380311370912608000000000000)
      constant := (79705879741651091781305134831754645550999580200099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605927780238281734091/100000000000000000000)
  centralHi := (151481945059570433523/25000000000000000000)
  directionLo := (15199631647202815627/2500000000000000000)
  directionHi := (607985265888112625081/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree149.table
  base := (114395992693289892881398562797100951695451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-897871046604262912722237670200888000000000000)
      constant := (33478559315575613242125067267589444854502498459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree149.table
  base := (915167941544229866153925216624059814107/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2161640512537335483640977161221415463000000000000)
      constant := (80804975435823597724433263872555020816003695495375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15199631647202815627/2500000000000000000)
  centralHi := (607985265888112625081/100000000000000000000)
  directionLo := (610035812235303580831/100000000000000000000)
  directionHi := (19063619132353236901/3125000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree150.table
  base := (116737188671686822079962331090054740656483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-903898716087424360615064892953868000000000000)
      constant := (33937098859703923669814421910201525054836848547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree150.table
  base := (11673718867146218212838961116754691387599/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2176152223004261826274574011071918318000000000000)
      constant := (81911625974316308904452057973709990226794714973910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (610035812235303580831/100000000000000000000)
  centralHi := (19063619132353236901/3125000000000000000)
  directionLo := (612079489022573053333/100000000000000000000)
  directionHi := (306039744511286526667/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree151.table
  base := (1488758854252908740930833467379281530953/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-909926385570585808507892115706848000000000000)
      constant := (34398769070790666044568332786020590793978942160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree151.table
  base := (59550354170019740294910174467001271196967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2190663933471188168908170860922421173000000000000)
      constant := (83025831357137513851431431666752126858619244539406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612079489022573053333/100000000000000000000)
  centralHi := (306039744511286526667/50000000000000000000)
  directionLo := (614116364832172248591/100000000000000000000)
  directionHi := (38382272802010765537/6250000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree152.table
  base := (121486551699286441180238183702901572024849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-915954055053747256400719338459828000000000000)
      constant := (34863569948839217413761307705131096891181804241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree152.table
  base := (3037163792478006396882258002558210210489/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2205175643938114511541767710772924028000000000000)
      constant := (84147591584295336907174752607189960091561955736040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614116364832172248591/100000000000000000000)
  centralHi := (38382272802010765537/6250000000000000000)
  directionLo := (308073253556369791113/50000000000000000000)
  directionHi := (616146507112739582227/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree153.table
  base := (61947359374599898654761876397773173537007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-921981724536908704293546561212808000000000000)
      constant := (35331501493852887388554077775675409579619397726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree153.table
  base := (24778943749811373835722560549446788473129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2219687354405040854175364560623426883000000000000)
      constant := (85276906655797738266582707304328753340462767485805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308073253556369791113/50000000000000000000)
  centralHi := (616146507112739582227/100000000000000000000)
  directionLo := (154542495551340345857/25000000000000000000)
  directionHi := (618169982205361383429/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree154.table
  base := (25265041898063473724989962444600035207941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-928009394020070152186373783965788000000000000)
      constant := (35802563705834918319403995054515920656357584345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree154.table
  base := (126325209490194448036022560920331998366247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-45595899283101371363448192050488362000000000000)
      constant := (1763546460645969687937398431407578960358772883127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154542495551340345857/25000000000000000000)
  centralHi := (618169982205361383429/100000000000000000000)
  directionLo := (62018685536886733527/10000000000000000000)
  directionHi := (620186855368867335271/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree155.table
  base := (128778023922976653093405780099470945589389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-934037063503231600079201006718768000000000000)
      constant := (36276756584788485724681522076689212127050561101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree155.table
  base := (128778023922870943697385164466818460307341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2248710775338893539442558260324432593000000000000)
      constant := (87558201331867300893951474448280756062544283297069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62018685536886733527/10000000000000000000)
  centralHi := (620186855368867335271/100000000000000000000)
  directionLo := (1944366221263712309/312500000000000000)
  directionHi := (622197190804387938881/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree156.table
  base := (65626581023754056595934907090671888472573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-940064732986393047972028229471748000000000000)
      constant := (36754080130716698925832546328525111597276878714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree156.table
  base := (131253162047417208812178627926405689658653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2263222485805819882076155110174935448000000000000)
      constant := (88710180936449571116821592904025687170729836850877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1944366221263712309/312500000000000000)
  centralHi := (622197190804387938881/100000000000000000000)
  directionLo := (78025131459900018307/12500000000000000000)
  directionHi := (624201051679200146457/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree157.table
  base := (133750623864235261178857255993046292022511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-946092402469554495864855452224728000000000000)
      constant := (37234534343622601849697438658426958561639805999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree157.table
  base := (133750623864157091470186819792563100267401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2277734196272746224709751960025438303000000000000)
      constant := (89869715385406641432653818687396946351583758397609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78025131459900018307/12500000000000000000)
  centralHi := (624201051679200146457/100000000000000000000)
  directionLo := (626198500149886220423/100000000000000000000)
  directionHi := (78274812518735777553/12500000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree158.table
  base := (136270409373474758594478091063472532905547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-952120071952715943757682674977708000000000000)
      constant := (37718119223509173964707093920236117062108291723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree158.table
  base := (34067602343351885563741037837025752196889/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2292245906739672567343348809875941158000000000000)
      constant := (91036804678745672074933784755674248195946756684004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626198500149886220423/100000000000000000000)
  centralHi := (78274812518735777553/12500000000000000000)
  directionLo := (628189597384829840249/100000000000000000000)
  directionHi := (2512758389539319361/400000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree159.table
  base := (1388125185755365270050646215946441734473/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-958147741435877391650509897730688000000000000)
      constant := (38204834770379331322879132745371409027965645700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree159.table
  base := (138812518575478731494205951690027373129087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2306757617206598909976945659726444013000000000000)
      constant := (92211448816473670104325989237745925807980562578783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628189597384829840249/100000000000000000000)
  centralHi := (2512758389539319361/400000000000000000)
  directionLo := (630174403586072491721/100000000000000000000)
  directionHi := (315087201793036245861/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree160.table
  base := (28275390294144773495817697793323299068443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-964175410919038839543337120483668000000000000)
      constant := (38694680984235927683966804807577774604674900935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree160.table
  base := (70688475735337087169357824425283388188677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2321269327673525252610542509576946868000000000000)
      constant := (93393647798597492234333868733518952580241791610186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630174403586072491721/100000000000000000000)
  centralHi := (315087201793036245861/50000000000000000000)
  directionLo := (632152978010552233259/100000000000000000000)
  directionHi := (31607648900527611663/5000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree161.table
  base := (14396370805933358668168133137006249846091/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-970203080402200287436164343236648000000000000)
      constant := (39187657865081755701882333690591256048018702190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree161.table
  base := (71981854029645430841122785836111500693963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-47669000778376563168247742029131627000000000000)
      constant := (1930273502553547914059410207094800936157890790966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (632152978010552233259/100000000000000000000)
  centralHi := (31607648900527611663/5000000000000000000)
  directionLo := (317062689495373018813/50000000000000000000)
  directionHi := (634125378990746037627/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree162.table
  base := (146572788341656127815800358176692866108757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-976230749885361735328991565989628000000000000)
      constant := (39683765412919548156722343777390279177217294613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree162.table
  base := (23451646134659103241273564590091443089/1600000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2350292748607377937877736209277952578000000000000)
      constant := (95780710296059301754427008324922040448791167506250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317062689495373018813/50000000000000000000)
  centralHi := (634125378990746037627/100000000000000000000)
  directionLo := (636091663954736052829/100000000000000000000)
  directionHi := (63609166395473605283/10000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree163.table
  base := (37301048079493926231932616412961635009987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-982258419368523183221818788742608000000000000)
      constant := (40183003627751979218448329656935418095235870732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree163.table
  base := (149204192317944125522038406830722613955497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2364804459074304280511333059128455433000000000000)
      constant := (96985573811410277894596312844415167626747158326473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (636091663954736052829/100000000000000000000)
  centralHi := (63609166395473605283/10000000000000000000)
  directionLo := (638051889445719311003/100000000000000000000)
  directionHi := (159512972361429827751/25000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree164.table
  base := (75928959994285219670347877252214076090839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-988286088851684631114646011495588000000000000)
      constant := (40685372509581665730590506892796756483877408302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree164.table
  base := (75928959994271645584097470221017668237123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2379316169541230623144929908978958288000000000000)
      constant := (98197992171183061902252843274312924306607719654214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (638051889445719311003/100000000000000000000)
  centralHi := (159512972361429827751/25000000000000000000)
  directionLo := (640006111140979636461/100000000000000000000)
  directionHi := (320003055570489818231/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree165.table
  base := (38633492838428124297319079944639488663783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-994313758334846079007473234248568000000000000)
      constant := (41190872058411168504309139599244421795350136988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree165.table
  base := (154533971353689159314739829373639580110469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2393827880008156965778526758829461143000000000000)
      constant := (99417965375383804566316755052007530071406826173221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (640006111140979636461/100000000000000000000)
  centralHi := (320003055570489818231/50000000000000000000)
  directionLo := (641954383870339762001/100000000000000000000)
  directionHi := (320977191935169881001/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree166.table
  base := (78616173206834113602282409630617236678551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-1000341427818007526900300457001548000000000000)
      constant := (41699502274242993614815078593396283159816972718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree166.table
  base := (157232346413648165573526856407535199109439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2408339590475083308412123608679963998000000000000)
      constant := (100645493424018524936093357491011188666398128433951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641954383870339762001/100000000000000000000)
  centralHi := (320977191935169881001/50000000000000000000)
  directionLo := (160974190408527738547/25000000000000000000)
  directionHi := (643896761634110954189/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree167.table
  base := (7997652258434914902511266968995478574367/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-1006369097301168974793127679754528000000000000)
      constant := (42211263157079593693564739264448235158124382060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree167.table
  base := (4998532661521282917253955755968049407331/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2422851300942009651045720458530466853000000000000)
      constant := (101880576317093113468249767840223110377325697183328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160974190408527738547/25000000000000000000)
  centralHi := (643896761634110954189/100000000000000000000)
  directionLo := (645833297620556771863/100000000000000000000)
  directionHi := (80729162202569596483/12500000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree168.table
  base := (162696067619057834636824633923412852305767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-1012396766784330422685954902507508000000000000)
      constant := (42726154706923369210841644198799375527344961703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree168.table
  base := (32539213523808602372138655791413940979071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (76532806)
      previous := (38266403)
      next := (38266403)
      square := (304782053760280445049019039839510000000000000)
      linear := (-49742102273651754973047292007774892000000000000)
      constant := (2104555388869659900908760898357218789814659364555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell048.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645833297620556771863/100000000000000000000)
  centralHi := (80729162202569596483/12500000000000000000)
  directionLo := (20242626381965216751/3125000000000000000)
  directionHi := (647764044222886936033/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree169.table
  base := (165461413764996552949399114314278258082563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1561894)
      previous := (780947)
      next := (780947)
      square := (6220041913475111123449368159990000000000000)
      linear := (-1018424436267491870578782125260488000000000000)
      constant := (43244176923776669744349000991524326130298835267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree169.table
  base := (16546141376498381239647794954469222131143/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (3750107494)
      previous := (1875053747)
      next := (1875053747)
      square := (14934320634253741807401932952135990000000000000)
      linear := (-2451874721875862336312914158231472563000000000000)
      constant := (104373406636584832550556045244791251965251506932870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell048.Kernel169
