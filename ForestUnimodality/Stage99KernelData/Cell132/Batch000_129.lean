import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell132.Parameters
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch000_049
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch050_099
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch100_149
import ForestUnimodality.BinomialMassData.Q28_53.Batch000_049
import ForestUnimodality.BinomialMassData.Q28_53.Batch050_099
import ForestUnimodality.BinomialMassData.Q28_53.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel000
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
  base := (5765190549697289495000518469/100000000000000000000000000)
  polynomial :=
    { denominator := 447320000000000000000000000000000000000000000
      center := (2929593)
      previous := (0)
      next := (2617175)
      square := (67756330679037134043785071236800000000000000)
      linear := (-315147775615050323603227868020400000000000000)
      constant := (25788850366905915369036319215530800000000000000) }

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
  base := (5765190549697289495000518469/100000000000000000000000000)
  polynomial :=
    { denominator := 132500000000000000000000000000000000000000
      center := (868)
      previous := (0)
      next := (775)
      square := (20070003163221899894486099300000000000000)
      linear := (-93349459601614432346927686025000000000000)
      constant := (7638877478348908580875686971425000000000000) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel001
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
  base := (346920485127960980637090394691512192093011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-4324694639473238553672374821458547000000000000000)
      constant := (175615564738483335587487629010679568527937184525516) }

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
  base := (86714998634933830954106587560859526606817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-6071441536025991308478388920125000000000000)
      constant := (246493100609468032793861211777554410238548953) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel002
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
  base := (54509200334128628288170767480127340542299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-5125091704243369338489852394844960800000000000000)
      constant := (113638564007662395375734623143256239185382333203376) }

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
  base := (217969096292721729566940644152697842955241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-28781446852665670810278441923700000000000000)
      constant := (637935623638516131808237384860928240861271969) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel003
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
  base := (36020443500987504757422340830543451452357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-5925488769013500123307329968231374600000000000000)
      constant := (79561701556877606343775038865579477201099188249168) }

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
  base := (144023783873027916087831209275997488341783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-33277127561227376386643328166900000000000000)
      constant := (446616072028850976929511525335076944752068447) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel004
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
  base := (100294260610345109076280907151010945648271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-6725885833783630908124807541617788400000000000000)
      constant := (60998514063738303243652161593826746984718179974076) }

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
  base := (50124412468025700014611786793493679543913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-18886404134894540981504107205050000000000000)
      constant := (171210059976444145404734938305323745838851617) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel005
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
  base := (73250905655770735066890654871581052397439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-7526282898553761692942285115004202200000000000000)
      constant := (51234129610298620845982905028152796795873784994684) }

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
  base := (9152026347178378790188572175654181024127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-10567122244587696884843275163325000000000000)
      constant := (71907122740016591023395077286325188993545486) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel006
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
  base := (27824641967506139440352314914158018164159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-8326679963323892477759762688390616000000000000000)
      constant := (46615597938059118040690724430144529409899541238008) }

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
  base := (5562257974230712190308249235450089779733/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-23382084843456246557868993448250000000000000)
      constant := (130863021080959024721898974965096510956349985) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel007
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
  base := (43496308584249897382481577099192225354933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-9127077028094023262577240261777029800000000000000)
      constant := (45145425436132106145561902870733883718893058436948) }

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
  base := (43475178546148281751301971296595988912689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-51259850395474198692102873139700000000000000)
      constant := (253497129582160955859517636854138132855743401) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel008
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
  base := (17295824928553938137485032616080053112067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-9927474092864154047394717835163443600000000000000)
      constant := (45722923649664599432499407862273499202303670030104) }

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
  base := (34574302859819600223008754991394767523591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-55755531104035904268467759382900000000000000)
      constant := (256762783760266358153107819711627901973767119) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel009
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
  base := (1731803006525775397759882462741548587883/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-10727871157634284832212195408549857400000000000000)
      constant := (47734570910637414501556681679604858856286452594368) }

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
  base := (13847032785210403691561933064712452249101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-30125605906298804922416322813050000000000000)
      constant := (134039743898048699038465825620177278367724709) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel010
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
  base := (22152593704360597705231176067967906389497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-11528268222404415617029672981936271200000000000000)
      constant := (50832546955052740651846734255275563940881319148132) }

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
  base := (5534897201115632956881202129997398829673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-16186723130289828855299382967325000000000000)
      constant := (71373832435755607839202259910162693312551457) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel011
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
  base := (17518983516229220994730393269522468431967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-12328665287174546401847150555322685000000000000000)
      constant := (54814804101373209294888010759615870710731697139452) }

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
  base := (17507265521874998127543195436595177565483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-69242573229721020997562418112500000000000000)
      constant := (307876577425485458813610486597795853781441747) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel012
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
  base := (13565402842107212953169183727350082030477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-13129062351944677186664628128709098800000000000000)
      constant := (59559977269020232665963484041673508331358144185012) }

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
  base := (13554672413413265229943361509430964115071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-73738253938282726573927304355700000000000000)
      constant := (334542263767817441028797008087991578199234439) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel013
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
  base := (1267460077445307895097575319852006189331/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-13929459416714807971482105702095512600000000000000)
      constant := (64991944716760423459922635596994635745452307579488) }

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
  base := (1266219605739008144569289128618805316231/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-19558483661711108037573047649725000000000000)
      constant := (91266318230864285062921570695280448266585758) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel014
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
  base := (7141337877262311224464035252826585893691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-14729856481484938756299583275481926400000000000000)
      constant := (71060443049353349045678657520205758624918419135596) }

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
  base := (7132110476443716988567684560534087715661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-82729615355406137726657076842100000000000000)
      constant := (399163557857120700781345612171340252393291749) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel015
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
  base := (900049066275724307217632689357039553337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-15530253546255069541117060848868340200000000000000)
      constant := (77730390937201079011329122134016340258112269295860) }

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
  base := (4491644673122484007929131162471157544481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-87225296063967843303021963085300000000000000)
      constant := (436640239601841088176760341317381481542447129) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel016
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
  base := (108237452814883877325946539845129686659/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-16330650611025200325934538422254754000000000000000)
      constant := (84975949126135231744771835523020392220184372580080) }

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
  base := (1078364014407006942874438824479929227121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-45860488386264774439693424664250000000000000)
      constant := (238675142767488953373039545861164121198982889) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel017
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
  base := (94964508284784441326085410122015980353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-17131047675795331110752015995641167800000000000000)
      constant := (92777165853521970905752409175670071390861120878468) }

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
  base := (43743959419090311928212548634868740013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-48108328740545627227875867785850000000000000)
      constant := (260590846726902341280220465956115346290696517) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel018
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
  base := (-1741092879611666680238186754687076083981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-17931444740565461895569493569027581600000000000000)
      constant := (101118041224965878506849349724562136215132860217164) }

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
  base := (-1748054269664703093394169900451115568781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-100712338189652960032116621814900000000000000)
      constant := (568044635434798553950196406854432816367294171) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel019
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
  base := (-3369807788814179580823155296500877462239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-18731841805335592680386971142413995400000000000000)
      constant := (109985376621362450093432677400611795212333095456516) }

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
  base := (-105508764413851583668038471098076281489/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-26302004724553666402120377014525000000000000)
      constant := (154466251162975616460698760297184029802379192) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel020
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
  base := (-4813386587703030370518334052055302426083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-19532238870105723465204448715800409200000000000000)
      constant := (119368063574382953313475582825096556915414398993652) }

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
  base := (-963879172066706452794772226587536252589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-109703699606776371184846394301300000000000000)
      constant := (670580426685855497226546817413578053332387495) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel021
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
  base := (-3045389293423155729219553183248606040017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-20332635934875854250021926289186823000000000000000)
      constant := (129256622919641196421423070865283713005635283429496) }

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
  base := (-6096349308383412932580275369549215966641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-114199380315338076761211280544500000000000000)
      constant := (726137674241030595093427766763336252349705431) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel022
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
  base := (-7218305364164239710347976447872028044317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-21133032999645985034839403862573236800000000000000)
      constant := (139642889984359675401269380034699223016536186503948) }

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
  base := (-7223462129246511037029999624260212421159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-118695061023899782337576166787700000000000000)
      constant := (784490900718722945487519515155453063308964369) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel023
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
  base := (-41050570332095115408039138830360005903/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-21933430064416115819656881435959650600000000000000)
      constant := (150519787828758831327376842268097999836837069146400) }

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
  base := (-4107440596262992638376284715063577943947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-61595370866230743956970526515450000000000000)
      constant := (422800183781108637811062248638786409555452877) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel024
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
  base := (-9078520049201782284357270437678642552607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-22733827129186246604474359009346064400000000000000)
      constant := (161881155844530348802955974852080386664629251848708) }

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
  base := (-9082921450843079303498373829074339170631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-127686422441023193490305939274100000000000000)
      constant := (909431482069600512079475870310930181269697521) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel025
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
  base := (-4917138225086766040436835874537607199059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-23534224193956377389291836582732478200000000000000)
      constant := (173721614904070095182439321670244753765473681433192) }

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
  base := (-9838335483237824832923663223902864540777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-132182103149584899066670825517300000000000000)
      constant := (975954040246349205770295226874056853504957407) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel026
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
  base := (-10486792919543380914085997189786878051223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-24334621258726508174109314156118892000000000000000)
      constant := (186036457943190791085753754372916495023034943179812) }

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
  base := (-10490532232619158840058886314567131243509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-136677783858146604643035711760500000000000000)
      constant := (1045141612371832152731722036568780928336983219) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel027
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
  base := (-43141863781021971123126373249513142417/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-25135018323496638958926791729505305800000000000000)
      constant := (198821559163994576098463237586272845122648853209088) }

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
  base := (-11047758537148085107665694648569277767747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-141173464566708310219400598003700000000000000)
      constant := (1116971033077655093337978820198168898750398677) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel028
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
  base := (-5757043888780572675352049083283021412077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-25935415388266769743744269302891719600000000000000)
      constant := (212073297492892390116329798471432274398636735610776) }

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
  base := (-1151725217041317518937757418094332309751/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-72834572637635007897882742123450000000000000)
      constant := (595710985728903865047454557857265102709547205) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel029
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
  base := (-11902464994285166455452507607850338186527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-26735812453036900528561746876278133400000000000000)
      constant := (225788491353512506815159415426874365627912986781188) }

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
  base := (-2976343065608936667073864281163881476879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-37541206495957930343032592622525000000000000)
      constant := (317119141179015045477895601132910656931446889) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel030
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
  base := (-47715008864298325514996071807303028799/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-27536209517807031313379224449664547200000000000000)
      constant := (239964342669276805189717853769706042667250650919936) }

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
  base := (-97741690138319611461768014708210743197/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-154660506692393426948495256733300000000000000)
      constant := (1348119103648918156133759328319579502794953375) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel031
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
  base := (-778546440716489048100491489830761029363/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-28336606582577162098196702023050961000000000000000)
      constant := (254598388544132528058703852430870117824201950367552) }

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
  base := (-6229595788930116522222050286354576456323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-79578093700477566262430071488250000000000000)
      constant := (715167880627384625398186039873829994734188693) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel032
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
  base := (-6315952197546370732928609359073993441019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-29137003647347292883014179596437374800000000000000)
      constant := (269688459418952999521147897361014538936614497765672) }

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
  base := (-6317074595702463469671243805652937465797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-81825934054758419050612514609850000000000000)
      constant := (757557178858657400830020051605920898658576227) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel033
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
  base := (-6372174792844061230668409091466000088463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-29937400712117423667831657169823788600000000000000)
      constant := (285232642741193984862231456331601680750752899396744) }

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
  base := (-1274640635010045611989936955695666581039/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-84073774409039271838794957731450000000000000)
      constant := (801222078179140618255394035682654362869307245) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel034
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
  base := (-1599681415245765379458386102021121594751/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-30737797776887554452649134743210202400000000000000)
      constant := (301229251358943510740698598692140817891914395448352) }

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
  base := (-6399667366991582238533039171543980388633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-86321614763320124626977400853050000000000000)
      constant := (846157843064223232679466846403532959088329903) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel035
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
  base := (-12794186768101117091028830711881840103431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-31538194841657685237466612316596616200000000000000)
      constant := (317676795981680311928142657061153309299390847972964) }

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
  base := (-1599488815190697397611077076962368851217/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-44284727558800488707579921987325000000000000)
      constant := (446180146735620289845954436526125411793862894) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel036
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
  base := (-12737185585596408363907946105524313465411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-32338591906427816022284089889983030000000000000000)
      constant := (334573961152909003876176761081559959723759524660084) }

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
  base := (-6369381213729946863458910606763719565143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-90817295471881830203342287096250000000000000)
      constant := (939825737370351293528218965288800711741513313) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel037
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
  base := (-6314385944029781065328798087220886477403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-33138988971197946807101567463369443800000000000000)
      constant := (351919584262789026344821430271866962712321766183464) }

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
  base := (-12630213661596651308479887003452433560579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-186130271652325365983049460435700000000000000)
      constant := (1977101823626752932546740964845302114128333589) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel038
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
  base := (-12471000925690787565417631489029569503549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-33939386035968077591919045036755857600000000000000)
      constant := (369712637197161158106032497724594313802984713494156) }

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
  base := (-12472318615821687994966072527092596354179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-190625952360887071559414346678900000000000000)
      constant := (2077065862813824882335806803664196896841111189) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel039
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
  base := (-12265691192271455441418017251230363571881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-34739783100738208376736522610142271400000000000000)
      constant := (387952210276413207533331266129171089297915389484764) }

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
  base := (-12266894972376100290969753866750302581659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-195121633069448777135779232922100000000000000)
      constant := (2179538486432503196342232653619098400048119869) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel040
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
  base := (-1501806568904955518059449996772671644763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-35540180165508339161554000183528685200000000000000)
      constant := (406637498185749471162428936795499800118116790204576) }

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
  base := (-6007775915135524561549210887637429522507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-99808656889005241356072059582650000000000000)
      constant := (1142257587261832761761589036592626460471277837) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel041
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
  base := (-2929677723927741595221723395565302225903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-36340577230278469946371477756915099000000000000000)
      constant := (425767787639312320421440113268123751506218132102928) }

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
  base := (-5859857182456962489156563070205929806411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-102056497243286094144254502704250000000000000)
      constant := (1195995961884796252000384736613991543173791501) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel042
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
  base := (-11379729787533444687096100659785569994357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-37140974295048600731188955330301512800000000000000)
      constant := (445342446555505620934092012138214940442727922785708) }

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
  base := (-5690322733106408550000240679505527144753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-104304337597566946932436945825850000000000000)
      constant := (1250982593356266157545166926953268974250388823) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel043
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
  base := (-549931473035024598572308225695741104533/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-37941371359818731516006432903687926600000000000000)
      constant := (465360914550766266109651144098775585445514594909040) }

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
  base := (-10999464740627667049374250265968517710441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-213104355903695599441238777894900000000000000)
      constant := (2614431818377938980946421755417694433751371231) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel044
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
  base := (-1057640352312224057664957132340828079527/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-38741768424588862300823910477074340400000000000000)
      constant := (485822694584704225913309523568064875861500080731880) }

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
  base := (-2644291302821110852941067241288725830947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-54400009153064326254400916034525000000000000)
      constant := (682347257340962913953210417036419969140869877) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel045
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
  base := (-2528483411648720101482378584842855557153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-39542165489358993085641388050460754200000000000000)
      constant := (506727345611622311459290942542356813575796168402928) }

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
  base := (-10114628006084749258595508413916720983949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-222095717320819010593968550381300000000000000)
      constant := (2846834344581994736661960848671307930756087259) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel046
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
  base := (-4806001248375482503725903743420004247937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-40342562554129123870458865623847168000000000000000)
      constant := (528074476112464262713600386714715171726001355806456) }

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
  base := (-150197426338553040637768218609053691293/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-56647849507345179042583359156125000000000000)
      constant := (741691391735783451543255750389434690898527408) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel047
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
  base := (-1133913140241681167132085037669725376141/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-41142959618899254655276343197233581800000000000000)
      constant := (549863738397667678702128269399708708754313159937632) }

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
  base := (-4535940815111296486511356258593755719307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-115543539368971210873349161433850000000000000)
      constant := (1544590372685757277263677533634610140184466637) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel048
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
  base := (-1698491798312790043195703218260433610091/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-41943356683669385440093820770619995600000000000000)
      constant := (572094823585591197324005085294234215276071885930020) }

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
  base := (-2123246018943601264535992748907109102263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-58895689861626031830765802277725000000000000)
      constant := (803519536653236348816650388747519930531743233) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel049
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
  base := (-3938006425018388037430299729928672213251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-42743753748439516224911298344006409400000000000000)
      constant := (594767457173460643271852269943268535578748647290088) }

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
  base := (-7876490965997755814879087514991396554619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-240078440155065832899428095354100000000000000)
      constant := (3341456230370043464181779372357189167078075229) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel050
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
  base := (-7222454530924839993120409148483586315341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-43544150813209647009728775917392823200000000000000)
      constant := (617881395128406634329856358110510139657064246717004) }

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
  base := (-902861220547819155106373141289755217247/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-61143530215906884618948245399325000000000000)
      constant := (867828406839466402426891432127234155189506354) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel051
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
  base := (-326610892893565393184911055284725224557/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-44344547877979777794546253490779237000000000000000)
      constant := (641436420435376648718363991325398617619169306290160) }

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
  base := (-6532613953138439413923945525207812222577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-249069801572189244052157867840500000000000000)
      constant := (3603649119924884947247239856196091255466781207) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel052
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
  base := (-2902844371284216698517613093380187598769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-45144944942749908579363731064165650800000000000000)
      constant := (665432340046694556940230652416287674649390494647672) }

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
  base := (-1161209825851180753453612545843159992307/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-253565482280750949628522754083700000000000000)
      constant := (3738461624929155191983026961289632817908048185) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel053
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
  base := (-5043210576355953728801683422411303790103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94384520000000000000000000000000000000000000000
      center := (618144123)
      previous := (0)
      next := (552223925)
      square := (14296585773276835283238650030964800000000000000)
      linear := (-866893245424906403097758653538718200000000000000)
      constant := (13016395890282612467719459553125553616169694759444) }

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
  base := (-5043538394266100243800572901902672350497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (3472)
      previous := (0)
      next := (3100)
      square := (80280012652887599577944397200000000000000)
      linear := (-4869078546968163305752596987300000000000000)
      constant := (73127361860348591179042877875799158365423659) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel054
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
  base := (-4245088999917337426364118568073845035711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-46745739072290170148998686210938478400000000000000)
      constant := (714746193957157591505936423876782682977275182353284) }

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
  base := (-530673390273025790291002631594002319241/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-65639210924468590195313131642525000000000000)
      constant := (1003878480784309183807002242411904894970504062) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel055
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
  base := (-3411596125065798707982699210268594499971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-47546136137060300933816163784324892200000000000000)
      constant := (740063839242574703356313250989974182732591664900724) }

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
  base := (-3411867179632085231918571418042473283061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-267052524406436066357617412813300000000000000)
      constant := (4157752094872098586388783814640718692547881651) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel056
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
  base := (-2542974273481005604841313893227548552453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-48346533201830431718633641357711306000000000000000)
      constant := (765821796822728064717583864989730411469230152493932) }

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
  base := (-2543220663002914913753217913201643981681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-271548205114997771933982299056500000000000000)
      constant := (4302464013754292449134819650488216582055458071) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel057
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
  base := (-819719644649680474806261909180415975991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-49146930266600562503451118931097719800000000000000)
      constant := (792019958724188066851539533843373064060131034171208) }

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
  base := (-51239475299086324180302146729528376459/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-69010971455889869377586796324925000000000000)
      constant := (1112412268514678867311609363744194038324213352) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel058
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
  base := (-701183475518681883141906303264558371597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-49947327331370693288268596504484133600000000000000)
      constant := (818658228749696149039181901841907897767949628264268) }

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
  base := (-175346733126194305146421735769762832681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-70134891633030295771678017885725000000000000)
      constant := (1149826684034868876368257482834422736202999071) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel059
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
  base := (33952725235384171326027327968557469823/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-50747724396140824073086074077870547400000000000000)
      constant := (845736521175485769517502667793353849174032313614304) }

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
  base := (67859244078610139836132954743548085993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-71258811810170722165769239446525000000000000)
      constant := (1187859129779644988113161811085574626573554337) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel060
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
  base := (319705950878030150291453971714332370721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-51548121460910954857903551651256961200000000000000)
      constant := (873254759595514780993950227076221969764136429145104) }

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
  base := (639327968538087134410406432347880364449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-144765463974622297119720922014650000000000000)
      constant := (2453018997199670253491427051592465195943737241) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel061
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
  base := (464057273167204757426485067839346961573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-52348518525681085642721029224643375000000000000000)
      constant := (901212875895616035933479441725096894058410440323940) }

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
  base := (1160066966225861462702161361828538059187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-147013304328903149907903365136250000000000000)
      constant := (2531555389954540424001989912323576363408256283) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel062
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
  base := (1697944040129482399362198344850519284847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-53148915590451216427538506798029788800000000000000)
      constant := (929610809342601721444699595796157142660180890105464) }

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
  base := (848937421931545949036588205597766791417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-74630572341592001348042904128925000000000000)
      constant := (1305663633746781703434792871586524126917090353) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel063
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
  base := (281595042227085834262564903057556829041/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-53949312655221347212355984371416202600000000000000)
      constant := (958448505775134283192504953920693986412462980483136) }

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
  base := (4505395054291973651895599673414777284019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-303017970074929710968536502758900000000000000)
      constant := (5384668955844039702897743076785422109390809371) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel064
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
  base := (2824543790480807427028173362416003038929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-54749709719991477997173461944802616400000000000000)
      constant := (987725916884735255573008037310033124363767262778248) }

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
  base := (176530424164428758641274079832661878331/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-76878412695872854136225347250525000000000000)
      constant := (1387288442881701221731145448677199577729854232) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel065
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
  base := (6826502647775364278935878695494220297769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-55550106784761608781990939518189030200000000000000)
      constant := (1017442999576670931138779035839408364577819675920164) }

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
  base := (6826399198692118887048638536748369860697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-312009331492053122121266275245300000000000000)
      constant := (5716108740332367622684315845671726170938697873) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel066
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
  base := (2009422253520331405508817803660508895707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-56350503849531739566808417091575444000000000000000)
      constant := (1047599715401654889412672600532650116126633147419568) }

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
  base := (4018797581155676418871795192862035796793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-158252506100307413848815580744250000000000000)
      constant := (2942766823309326188609536946049949458553191537) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel067
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
  base := (9282578093872243291330954322859990202681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-57150900914301870351625894664961857800000000000000)
      constant := (1078196030050363050656165290849437385479419169160036) }

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
  base := (4641246481876446118635687929493627875829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-160500346454588266636998023865850000000000000)
      constant := (3028714148984064784032049012530947600703203661) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel068
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
  base := (211222173561165730910763327963244585369/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-57951297979072001136443372238348271600000000000000)
      constant := (1109231912903685429318850852822040723925652803288200) }

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
  base := (5280515736077256442257406700808176735819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-162748186808869119425180466987450000000000000)
      constant := (3115896261332103603719225040784970168450915571) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel069
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
  base := (11873226134307667697140040349663483364389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-58751695043842131921260849811734685400000000000000)
      constant := (1140707336632456040414099882141392018062291956548884) }

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
  base := (11873156126615026572375246265760073684783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-329992054326299944426725820218100000000000000)
      constant := (6408626167445313857668389934819320046980555447) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel070
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
  base := (826180105920276998361331354329745365781/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-59552092108612262706078327385121099200000000000000)
      constant := (1172622276841122293105920930981746508023460156538176) }

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
  base := (6609409112220071438488732437942677575711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-167243867517430825001545353230650000000000000)
      constant := (3293964547752790628476626060556180981310172199) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel071
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
  base := (14598031821559803962202336495704770107607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-60352489173382393490895804958507513000000000000000)
      constant := (1204976711750449731140081954807780822234329225731292) }

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
  base := (912373392961073127914701967145658230487/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-84745853935855838894863898176125000000000000)
      constant := (1692425296178649398540637499646948615877751932) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel072
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
  base := (4002659410568066580734461778681235981467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-61152886238152524275713282531893926800000000000000)
      constant := (1237770621914917641357550274957999538451690823845808) }

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
  base := (8005292748578443555923468226548540942291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-171739548225992530577910239473850000000000000)
      constant := (3476971163015922313796476772928374851506895419) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel073
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
  base := (17456664446238971956289047390549199732971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-61953283302922655060530760105280340600000000000000)
      constant := (1271003989970954999238272042440155305498107158847276) }

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
  base := (17456617192648175514947896118248761394131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-347974777160546766732185365190900000000000000)
      constant := (7140652422094205045215982666422960770756113979) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel074
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
  base := (3787216247258623310018856760118860211221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-62753680367692785845348237678666754400000000000000)
      constant := (1304676800412602440802079525754530885320554606521380) }

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
  base := (18936038421802854795763992752068531894263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-352470457869108472308550251434100000000000000)
      constant := (7329831385957375508119008263617360506090984767) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel075
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
  base := (4089772065806494496855654087371693401271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-63554077432462916630165715252053168200000000000000)
      constant := (1338789039391571420578459519312391863002802464210380) }

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
  base := (20448821542338573408541753261616054336463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-356966138577670177884915137677300000000000000)
      constant := (7521479139974184890810008831521879496631124567) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel076
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
  base := (21994976998525603511802184068226626603611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-64354474497233047414983192825439582000000000000000)
      constant := (1373340694539012536703049011127959919836965588859116) }

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
  base := (1374683866611797522761198242037027314741/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-90365454821557970865320005980125000000000000)
      constant := (1928898903698682648845149208979128038908429876) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel077
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
  base := (11787204579322507927259676877264860752507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-65154871562003178199800670398825995800000000000000)
      constant := (1408331754806606515732865193061920287783167447111384) }

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
  base := (2946797167518902588532980065852540573771/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-91489374998698397259411227540925000000000000)
      constant := (1978045187118734614050956955641459572943445478) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel078
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
  base := (5037427415958000796511572487258693661279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-65955268626773308984618147972212409600000000000000)
      constant := (1443762210324858228037487040382640020876741816528620) }

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
  base := (25187108266900307395163952424033286822493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-370453180703355294614009796406900000000000000)
      constant := (8111234485681649930728522046167909502684382837) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel079
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
  base := (26833143136234413481538336849549311204951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-66755665691543439769435625545598823400000000000000)
      constant := (1479632052276710449116925038399990440314622585320156) }

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
  base := (13416558524299959808677554294498242286843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-187474430705958500095187341325050000000000000)
      constant := (4156378388491833505893171735000645562583741987) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel080
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
  base := (445506430949268105665536646173848072191/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-67556062756313570554253103118985237200000000000000)
      constant := (1515941272784803489484279586993778928738391442022144) }

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
  base := (7128096990943263301819136864533558046357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-94861135530119676441684892223325000000000000)
      constant := (2129186894554840198667653478708474764552216813) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel081
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
  base := (944529010736012893735315680085133327981/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-68356459821083701339070580692371651000000000000000)
      constant := (1552689864810892443666501356424356738069504177498752) }

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
  base := (3022490696605457523520346629284232325183/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-191970111414520205671552227568250000000000000)
      constant := (4361603424966245810490868204886497043007195235) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel082
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
  base := (15985340426428737239165550507979765860607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-69156856885853832123888058265758064800000000000000)
      constant := (1589877822066098432185947581327966796901937253198584) }

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
  base := (6394132300996571872138870203606884714579/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-388435903537602116919469341379700000000000000)
      constant := (8932134556868812782329410741781658695816262055) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel083
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
  base := (33749657874804303207083250148485614812573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-69957253950623962908705535839144478600000000000000)
      constant := (1627505138930816269094875352111529976555494840620788) }

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
  base := (33749640366077778526696935552433257038077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-392931584246163822495834227622900000000000000)
      constant := (9143530667526849601810377095437585019019958293) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel084
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
  base := (889046234263496463270659769114052887953/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-70757651015394093693523013412530892400000000000000)
      constant := (1665571810383230628951757680277724860101820229762720) }

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
  base := (7112366705622319896393796786564796037027/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-397427264954725528072199113866100000000000000)
      constant := (9357395153756973376721896029920102560340044215) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel085
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
  base := (3740724636866651661103498917690857422657/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-71558048080164224478340490985917306200000000000000)
      constant := (1704077831935507901944353678801017127226223657690920) }

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
  base := (3740723203570933919689557469579552588929/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-200961472831643616824282000054650000000000000)
      constant := (4786863995201767889866889615419244816111507805) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel086
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
  base := (1571433634054809449222816659907409214693/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-72358445144934355263157968559303720000000000000000)
      constant := (1743023199576833180506102167797911262845339787187700) }

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
  base := (4910728485702432169139742260575530821481/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-101604656592962234806232221588125000000000000)
      constant := (2448132288746350808522939228486513332155080258) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel087
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
  base := (41197625652753793905483363609463271135233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-73158842209704486047975446132690133800000000000000)
      constant := (1782407909722552684655317146067892513666012755503748) }

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
  base := (41197613925177308923914942903015652160693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-410914307080410644801293772595700000000000000)
      constant := (10013798627410740751915769421712570966919386637) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel088
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
  base := (5392824296007233590325716487483351842229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-73959239274474616832792923706076547600000000000000)
      constant := (1822231959168762703026447350476699532276683755551392) }

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
  base := (43142583761645158146183075388001723895167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-415409987788972350377658658838900000000000000)
      constant := (10237536389722348033447258983977696842421524103) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel089
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
  base := (22560370636298165148322666032619101455023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-74759636339244747617610401279462961400000000000000)
      constant := (1862495345051757947014004723784305548383084662905976) }

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
  base := (9024146336251209649993101860469307886013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-419905668497534055954023545082100000000000000)
      constant := (10463742425870253697119416875841091429259052585) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel090
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
  base := (23566030624679893864187837299497746147327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-75560033404014878402427878852849375200000000000000)
      constant := (1903198064811816098081755204898882562093691466687224) }

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
  base := (47132052576916451839126525570526812031691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-424401349206095761530388431325300000000000000)
      constant := (10692416721508632024476497862419609814997020019) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel091
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
  base := (49176549724355081288447937022959993349381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-76360430468785009187245356426235789000000000000000)
      constant := (1944340116160852167248707825652939611149117945305236) }

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
  base := (49176541883636181951484707360948650276743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-428897029914657467106753317568500000000000000)
      constant := (10923559263814425580341734343833304758627371087) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel092
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
  base := (410033620870796182007038087514185715319/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-77160827533555139972062833999622202800000000000000)
      constant := (1985921497053526871926311904989472528904446805995500) }

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
  base := (51254195520855104273921592316852916584011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-433392710623219172683118203811700000000000000)
      constant := (11157170041325340947429576559322039842684486899) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel093
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
  base := (3335313515486169626096580702788304663397/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-77961224598325270756880311573008616600000000000000)
      constant := (2027942205661438268561590677720843208764617732744512) }

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
  base := (53365009840926155617225989764283692898593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-437888391331780878259483090054900000000000000)
      constant := (11393249043795137525241530274282672893352147737) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel094
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
  base := (55508987373656935789648294909437482137811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-78761621663095401541697789146395030400000000000000)
      constant := (2070402240350065979673324562975854127249405084954316) }

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
  base := (55508981583094281161759514919495188425631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-442384072040342583835847976298100000000000000)
      constant := (11631796262064354364789231265857661984287597479) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel095
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
  base := (57686113065400496061456982190368406694959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-79562018727865532326515266719781444200000000000000)
      constant := (2113301599658173069867632749969055793808313005663804) }

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
  base := (14421526958095562599979249284029533741599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-111719938187226072353053215635325000000000000)
      constant := (2968202921986205106394204152425338960280151591) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel096
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
  base := (59896390711538034868627454286116664554593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-80362415792635663111332744293167858000000000000000)
      constant := (2156640282279402443883411613883020557054327252731908) }

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
  base := (11979277196571574318463533473622276465749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-451375433457465994988577748784500000000000000)
      constant := (12116295314116472181008365725563424872961444705) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel097
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
  base := (31069908988669229779189409340984009262107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-81162812857405793896150221866554271800000000000000)
      constant := (2200418287045832992122387423330332067050172947866584) }

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
  base := (7767476713101719900916651228453579487777/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-113967778541506925141235658756925000000000000)
      constant := (3090561783508790396281383668598952209562331186) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel098
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
  base := (32208196387718849513852942413232709944589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-81963209922175924680967699439940685600000000000000)
      constant := (2244635612913285978228154196332138936925044149240168) }

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
  base := (12883277783088256630246151568664662789361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-460366794874589406141307521270900000000000000)
      constant := (12610667141850279195995027833718695188876575245) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel099
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
  base := (66726113239590494968820563995849132814403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-82763606986946055465785177013327099400000000000000)
      constant := (2289292258948194688790132000504120947789699484080268) }

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
  base := (6672610975262532145820617630860394163723/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-232431237791575555858836203757050000000000000)
      constant := (6430777666165571818007450694008834236029489535) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel100
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
  base := (34534488850606798035845762249880407307123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-83564004051716186250602654586713513200000000000000)
      constant := (2334388224315870448757156440185535217391525347521176) }

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
  base := (69068974551526552180882644622171856084329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-469358156291712817294037293757300000000000000)
      constant := (13114911700801221249834973848223680743740880161) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel101
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
  base := (35722492334211261423655714184631090735811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-84364401116486317035420132160099927000000000000000)
      constant := (2379923508270016015521522560161798867143715261284632) }

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
  base := (1786124545591344769534102437525247128979/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-118463459250068630717600545000125000000000000)
      constant := (3342684060769835075022073791739184191853020110) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel102
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
  base := (1477082656145920040645321684611288406719/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-85164798181256447820237609733486340800000000000000)
      constant := (2425898110143353337881022595758694949230180461318200) }

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
  base := (36927065119080390978109454286407342175663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-239174758854418114223383533121850000000000000)
      constant := (6814514477713576827813762952868518224171437367) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel103
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
  base := (38148210462565326647281182467261152477927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-85965195246026578605055087306872754600000000000000)
      constant := (2472312029339246914744089703645086948523775075194424) }

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
  base := (76296418605130312232209646843381013111607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-482845198417397934023131952486900000000000000)
      constant := (13889789834502183863806342120901857265830504063) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel104
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
  base := (78771847955473923167724429348077204652157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-86765592310796709389872564880259168400000000000000)
      constant := (2519165265324216700593673294529192891585388708671092) }

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
  base := (39385922930316948828438488721647434697431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-243670439562979819799748419365050000000000000)
      constant := (7076509438657927906601142770401507644065083679) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel105
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
  base := (8128041294474593619206334831207720313919/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-87565989375566840174690042453645582200000000000000)
      constant := (2566457817621245847647084018092609825118795189095640) }

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
  base := (40640205526688976857899918276983382086277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-245918279917260672587930862486650000000000000)
      constant := (7209358040597992912457173698587046320280352093) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel106
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
  base := (41911057520140584318756185247168776276617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94384520000000000000000000000000000000000000000
      center := (618144123)
      previous := (0)
      next := (552223925)
      square := (14296585773276835283238650030964800000000000000)
      linear := (-1667290310195037187915236226925132000000000000000)
      constant := (49324333694411296172866486545384252336571176553768) }

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
  base := (327430130206123318691909360130172073803/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 132500000000000000000000000000000000000000
      center := (868)
      previous := (0)
      next := (775)
      square := (20070003163221899894486099300000000000000)
      linear := (-2341189813882467220529370807625000000000000)
      constant := (69277742659213456577539314371761543674339776) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel107
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
  base := (43198476739819455334544019562708426619811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-89166783505107101744324997600418409800000000000000)
      constant := (2662360869490473466879151379259299808718790487492632) }

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
  base := (86396951938237050581331286180641192960999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-500827921251644756328591497459700000000000000)
      constant := (14957514962851227685408204300083421111027446191) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel108
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
  base := (44502463790523802029973429320893022767493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-89967180569877232529142475173804823600000000000000)
      constant := (2710971368340222146052435620601818284807744323128616) }

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
  base := (89004926189712496735518840085730624397269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-505323601960206461904956383702900000000000000)
      constant := (15230616636579582912811348654781617323931928621) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel109
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
  base := (45823018367431267195703844755832833060923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-90767577634647363313959952747191237400000000000000)
      constant := (2760021182048077308854771729477792646332420689986776) }

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
  base := (11455754434885757688626985321231919495147/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-127454820667192041870330317486525000000000000)
      constant := (3876546615807535883930157004945380923723735846) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel110
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
  base := (9432028039592920598217910376823170154159/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-91567974699417494098777430320577651200000000000000)
      constant := (2809510310341331984662339654520777612988567030590040) }

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
  base := (9432027926259436954504071484823140938439/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-257157481688664936528843078094650000000000000)
      constant := (7892112220637739116379421301598341014480375755) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel111
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
  base := (97027658076756201033081791219586661708499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-92368371764187624883594907893964065000000000000000)
      constant := (2859438752976124463067735919122888416574173007588044) }

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
  base := (97027657054005032386386023398653432990591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-518810644085891578634051042432500000000000000)
      constant := (16064730569349760224749697061343217493270570119) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel112
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
  base := (2494204233535289249676151580295813243047/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-93168768828957755668412385467350478800000000000000)
      constant := (2909806509734385036669436876882342721682382499677280) }

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
  base := (49884084209262717255923125371445867345757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-261653162397226642105207964337850000000000000)
      constant := (8173852423115828527347062491632391441374231413) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel113
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
  base := (51270906900032975038098024748057240263417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-93969165893727886453229863040736892600000000000000)
      constant := (2960613580421106261847657800004132179286995243311304) }

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
  base := (10254181296735710095387404461081796638323/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-263901002751507494893390407459450000000000000)
      constant := (8316573635414516903204142928217293833785246535) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel114
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
  base := (105348591104113781287781399486488023047233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-94769562958498017238047340614123306400000000000000)
      constant := (3011859964861902405811385119172860514842628727375748) }

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
  base := (26337147588206779975641230943776024977747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-133074421552894173840786425290525000000000000)
      constant := (4230264460541319317654539498271266854162491323) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel115
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
  base := (21637700188362257715575043597740451840233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-95569960023268148022864818187509720200000000000000)
      constant := (3063545662900827399736921034123129436141622972418740) }

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
  base := (108188500264035384048762899493553588900309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-536793366920138400939510587405300000000000000)
      constant := (17211436559367069045892322220839392031220967981) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel116
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
  base := (13882692879297052471020069495975376200097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-96370357088038278807682295760896134000000000000000)
      constant := (3115670674398423879673098926749537291933340562253856) }

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
  base := (111061542422962926572651609414448066156559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-541289047628700106515875473648500000000000000)
      constant := (17504283421653453854433914377851584617833774231) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel117
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
  base := (7122982320781359607364653033544716058457/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-97170754152808409592499773334282547800000000000000)
      constant := (3168234999229978810852812333698234004787176499102272) }

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
  base := (113967716580992445118935835364339731021309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-545784728337261812092240359891700000000000000)
      constant := (17799598428326065693926910196272430304438856981) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel118
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
  base := (116907023013236597587327434200062570552711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-97971151217578540377317250907668961600000000000000)
      constant := (3221238637283963794401211191630751465440393940898716) }

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
  base := (23381404503159460854522809851446648492429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-550280409045823517668605246134900000000000000)
      constant := (18097381578760389045490570383708368178076165305) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel119
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
  base := (119879460477199141782084498618140134109777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-98771548282348671162134728481055375400000000000000)
      constant := (3274681588460640481423134111444245347064890726095812) }

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
  base := (14984932503569993797922418418892475376189/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-138694022438596305811242533094525000000000000)
      constant := (4599408218099486350230295711887037926663429802) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel120
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
  base := (61442514673041847899454416248224442577303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-99571945347118801946952206054441789200000000000000)
      constant := (3328563852670813597758093309791513536568218849425336) }

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
  base := (122885028941484821346167091891440085029587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-559271770462946928821335018621300000000000000)
      constant := (18700352308739307026265621020339055198848109883) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel121
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
  base := (7870233091276983789126890771710647136149/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-100372342411888932731769683627828203000000000000000)
      constant := (3382885429834715939788853730142964819455440871543104) }

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
  base := (1259237290955745410145558899025239125107/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-140941862792877158599424976216125000000000000)
      constant := (4751384971834462572982146802303147417560639075) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel122
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
  base := (128995560677638850811832655602141955049199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-101172739476659063516587161201214616800000000000000)
      constant := (3437646319881011361210944556452915050190655187197244) }

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
  base := (12899556034864150049969036138008150576581/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-284131565940035169987032395553850000000000000)
      constant := (9656597803897085102270643325868324474848080145) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel123
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
  base := (132100522870172503982724387603562957340251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-101973136541429194301404638774601030600000000000000)
      constant := (3492846522745903253708676031016988254703452356766956) }

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
  base := (6605026128676494440833406847463121536163/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-143189703147158011387607419337725000000000000)
      constant := (4905829867437771522761782148084319541975409335) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel124
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
  base := (67619307961989222549930289764623829242287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-102773533606199325086222116347987444400000000000000)
      constant := (3548486038372337349868313696054386082098109355290744) }

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
  base := (16904826957065735098493154729747267087257/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-144313623324298437781698640898525000000000000)
      constant := (4983977868222293954130597998660920146496209826) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel125
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
  base := (10813268729457471929969383913484067371/781250000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-103573930670969455871039593921373858200000000000000)
      constant := (3604564866709288861202123072463751484119262271052800) }

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
  base := (69204919747968027185839731215462620023217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (92008)
      previous := (0)
      next := (82150)
      square := (2127420335301521388815526525800000000000000)
      linear := (-290875087002877728351579724918650000000000000)
      constant := (10125485808461391279225771057159234499645216553) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel126
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
  base := (70807097109090987405075380624520398520149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-104374327735739586655857071494760272000000000000000)
      constant := (3661083007711125022868365000247964289747049521150888) }

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
  base := (141614194000816222627334579240268692660971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-586245854714317162279524336080500000000000000)
      constant := (20568499901596444095718612677112314757684667539) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel127
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
  base := (282913436105028769123263148017693433777/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-105174724800509717440674549068146685800000000000000)
      constant := (3718040461337035062955694606535052993711630653983744) }

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
  base := (18106459886229344265929633790363818450919/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (46004)
      previous := (0)
      next := (41075)
      square := (1063710167650760694407763262900000000000000)
      linear := (-147685383855719716963972305580925000000000000)
      constant := (5222124081670424968910957642780763932057262942) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel128
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
  base := (148122294866871586413366810739753923133729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-105975121865279848225492026641533099600000000000000)
      constant := (3775437227550520460025915847252741929651397709617924) }

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
  base := (148122294690256143675814498578457110637413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-595237216131440573432254108566900000000000000)
      constant := (21210960891974235864131147420535686023780493117) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell132.Kernel129
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
  base := (151426040896219388613769681852237959366593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757719045983672270011648451641134400000000000000)
      linear := (-106775518930049979010309504214919513400000000000000)
      constant := (3833273306318939108667449901511887175425405537003908) }

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
  base := (151426040737032104046373580643020805252023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (184016)
      previous := (0)
      next := (164300)
      square := (4254840670603042777631053051600000000000000)
      linear := (-599732896840002279008618994810100000000000000)
      constant := (21535893597291331422362467192381045441952932607) }

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
end ForestUnimodality.Stage99KernelData.Cell132.Kernel129
